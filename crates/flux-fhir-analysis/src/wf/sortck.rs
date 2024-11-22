use std::iter;

use ena::unify::InPlaceUnificationTable;
use flux_common::{bug, iter::IterExt, result::ResultExt, span_bug, tracked_span_bug};
use flux_errors::{ErrorGuaranteed, Errors};
use flux_middle::{
    fhir::{self, visit::Visitor as _, ExprRes, FhirId, FluxOwnerId},
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::{
        self,
        fold::{FallibleTypeFolder, TypeFoldable, TypeFolder, TypeSuperFoldable},
        AdtSortDef, WfckResults,
    },
};
use itertools::{izip, Itertools};
use rustc_data_structures::unord::UnordMap;
use rustc_errors::Diagnostic;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::{def_id::DefId, symbol::Ident, Span};

use super::errors;
use crate::conv;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(super) struct InferCtxt<'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    pub params: UnordMap<fhir::ParamId, (rty::Sort, fhir::ParamKind)>,
    pub wfckresults: WfckResults,
    sort_unification_table: InPlaceUnificationTable<rty::SortVid>,
    num_unification_table: InPlaceUnificationTable<rty::NumVid>,
    bv_size_unification_table: InPlaceUnificationTable<rty::BvSizeVid>,
    sort_of_bty: FxHashMap<FhirId, rty::Sort>,
    sort_of_alias_reft: UnordMap<FhirId, rty::FuncSort>,
}

impl<'genv, 'tcx> InferCtxt<'genv, 'tcx> {
    pub(super) fn new(genv: GlobalEnv<'genv, 'tcx>, owner: FluxOwnerId) -> Self {
        Self {
            genv,
            params: Default::default(),
            wfckresults: WfckResults::new(owner),
            sort_unification_table: InPlaceUnificationTable::new(),
            num_unification_table: InPlaceUnificationTable::new(),
            bv_size_unification_table: InPlaceUnificationTable::new(),
            sort_of_bty: Default::default(),
            sort_of_alias_reft: Default::default(),
        }
    }

    fn check_abs(
        &mut self,
        arg: &fhir::Expr,
        params: &[fhir::RefineParam],
        body: &fhir::Expr,
        expected: &rty::Sort,
    ) -> Result {
        if let Some(fsort) = self.is_coercible_from_func(expected, arg.fhir_id) {
            let fsort = fsort.expect_mono();
            self.insert_params(params)?;

            if params.len() != fsort.inputs().len() {
                return Err(self.emit_err(errors::ParamCountMismatch::new(
                    arg.span,
                    fsort.inputs().len(),
                    params.len(),
                )));
            }
            iter::zip(params, fsort.inputs()).try_for_each_exhaust(|(param, expected)| {
                let found = self.param_sort(param.id);
                if self.try_equate(&found, expected).is_none() {
                    return Err(self.emit_sort_mismatch(param.span, expected, &found));
                }
                Ok(())
            })?;
            self.check_expr(body, fsort.output())?;
            self.wfckresults
                .node_sorts_mut()
                .insert(arg.fhir_id, fsort.output().clone());
            Ok(())
        } else {
            Err(self.emit_err(errors::UnexpectedFun::new(arg.span, expected)))
        }
    }

    fn check_field_exprs(
        &mut self,
        expr_span: Span,
        sort_def: &AdtSortDef,
        sort_args: &[rty::Sort],
        field_exprs: &[fhir::FieldExpr],
        spread: &Option<&fhir::Spread>,
        expected: &rty::Sort,
    ) -> Result {
        let sort_by_field_name = sort_def.sort_by_field_name(sort_args);
        let mut used_fields = FxHashSet::default();
        for expr in field_exprs {
            // make sure that the field is actually a field
            if let Some(sort) = sort_by_field_name.get(&expr.ident.name) {
                self.check_expr(&expr.expr, sort)?;
            } else {
                return Err(self.emit_err(errors::FieldNotFound::new(expected.clone(), expr.ident)));
            }
            if let Some(old_field) = used_fields.replace(expr.ident) {
                return Err(self.emit_err(errors::DuplicateFieldUsed::new(expr.ident, old_field)));
            }
        }
        if let Some(spread) = spread {
            // must check that the spread is of the same sort as the constructor
            self.check_expr(&spread.expr, expected)?;
            Ok(())
        } else if sort_by_field_name.len() != used_fields.len() {
            // emit an error because all fields are not used
            let used_field_names: Vec<rustc_span::Symbol> =
                used_fields.into_iter().map(|k| k.name).collect();
            let fields_remaining = sort_by_field_name
                .into_keys()
                .filter(|x| !used_field_names.contains(x))
                .collect();
            return Err(
                self.emit_err(errors::ConstructorMissingFields::new(expr_span, fields_remaining))
            );
        } else {
            Ok(())
        }
    }

    fn check_constructor(
        &mut self,
        expr: &fhir::Expr,
        field_exprs: &[fhir::FieldExpr],
        spread: &Option<&fhir::Spread>,
        expected: &rty::Sort,
    ) -> Result {
        let expected = self.resolve_vars_if_possible(expected);
        if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = &expected {
            self.wfckresults
                .record_ctors_mut()
                .insert(expr.fhir_id, sort_def.did());
            self.check_field_exprs(expr.span, sort_def, sort_args, field_exprs, spread, &expected)?;
            Ok(())
        } else {
            Err(self.emit_err(errors::UnexpectedConstructor::new(expr.span, &expected)))
        }
    }

    fn check_record(
        &mut self,
        arg: &fhir::Expr,
        flds: &[fhir::Expr],
        expected: &rty::Sort,
    ) -> Result {
        if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = expected {
            let sorts = sort_def.field_sorts(sort_args);
            if flds.len() != sorts.len() {
                return Err(self.emit_err(errors::ArgCountMismatch::new(
                    Some(arg.span),
                    String::from("type"),
                    sorts.len(),
                    flds.len(),
                )));
            }
            self.wfckresults
                .record_ctors_mut()
                .insert(arg.fhir_id, sort_def.did());

            izip!(flds, &sorts)
                .map(|(arg, expected)| self.check_expr(arg, expected))
                .try_collect_exhaust()
        } else {
            Err(self.emit_err(errors::ArgCountMismatch::new(
                Some(arg.span),
                String::from("type"),
                1,
                flds.len(),
            )))
        }
    }

    pub(super) fn check_expr(&mut self, expr: &fhir::Expr, expected: &rty::Sort) -> Result {
        match &expr.kind {
            fhir::ExprKind::IfThenElse(p, e1, e2) => {
                self.check_expr(p, &rty::Sort::Bool)?;
                self.check_expr(e1, expected)?;
                self.check_expr(e2, expected)?;
            }
            fhir::ExprKind::Abs(refine_params, body) => {
                self.check_abs(expr, refine_params, body, expected)?;
            }
            fhir::ExprKind::Record(fields) => self.check_record(expr, fields, expected)?,
            fhir::ExprKind::Constructor(None, exprs, spread) => {
                self.check_constructor(expr, exprs, spread, expected)?;
            }
            fhir::ExprKind::UnaryOp(..)
            | fhir::ExprKind::BinaryOp(..)
            | fhir::ExprKind::Dot(..)
            | fhir::ExprKind::App(..)
            | fhir::ExprKind::Alias(..)
            | fhir::ExprKind::Var(..)
            | fhir::ExprKind::Literal(..)
            | fhir::ExprKind::Constructor(..) => {
                let found = self.synth_expr(expr)?;
                let found = self.resolve_vars_if_possible(&found);
                let expected = self.resolve_vars_if_possible(expected);
                if !self.is_coercible(&found, &expected, expr.fhir_id) {
                    return Err(self.emit_sort_mismatch(expr.span, &expected, &found));
                }
            }
        }
        Ok(())
    }

    pub(super) fn check_loc(&mut self, loc: &fhir::PathExpr) -> Result {
        let found = self.synth_var(loc);
        if found == rty::Sort::Loc {
            Ok(())
        } else {
            Err(self.emit_sort_mismatch(loc.span, &rty::Sort::Loc, &found))
        }
    }

    fn synth_expr(&mut self, expr: &fhir::Expr) -> Result<rty::Sort> {
        match &expr.kind {
            fhir::ExprKind::Var(var, _) => Ok(self.synth_var(var)),
            fhir::ExprKind::Literal(lit) => Ok(synth_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, e1, e2) => self.synth_binary_op(expr, *op, e1, e2),
            fhir::ExprKind::UnaryOp(op, e) => self.synth_unary_op(*op, e),
            fhir::ExprKind::App(f, es) => self.synth_app(f, es, expr.span),
            fhir::ExprKind::Alias(_alias_reft, func_args) => {
                // To check the application we only need the sort of `_alias_reft` which we collected
                // during early conv, but should we do any extra checks on _alias_reft?
                self.synth_alias_reft_app(expr.fhir_id, expr.span, func_args)
            }
            fhir::ExprKind::IfThenElse(p, e1, e2) => {
                self.check_expr(p, &rty::Sort::Bool)?;
                let sort = self.synth_expr(e1)?;
                self.check_expr(e2, &sort)?;
                Ok(sort)
            }
            fhir::ExprKind::Dot(var, fld) => {
                let sort = self.ensure_resolved_var(var)?;
                match &sort {
                    rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) => {
                        let (proj, sort) = sort_def
                            .field_by_name(sort_args, fld.name)
                            .ok_or_else(|| self.emit_field_not_found(&sort, *fld))?;
                        self.wfckresults
                            .field_projs_mut()
                            .insert(expr.fhir_id, proj);
                        Ok(sort)
                    }
                    rty::Sort::Bool | rty::Sort::Int | rty::Sort::Real => {
                        Err(self.emit_err(errors::InvalidPrimitiveDotAccess::new(&sort, *fld)))
                    }
                    _ => Err(self.emit_field_not_found(&sort, *fld)),
                }
            }
            fhir::ExprKind::Constructor(Some(path), field_exprs, spread) => {
                // if we have S then we can synthesize otherwise we fail
                // first get the sort based on the path - for example S { ... } => S
                // and we should expect sort to be a struct or enum app
                let path_def_id = match path.res {
                    ExprRes::Struct(def_id) | ExprRes::Enum(def_id) => def_id,
                    _ => span_bug!(expr.span, "unexpected path in constructor"),
                };
                let sort_def = match self.genv.adt_sort_def_of(path_def_id) {
                    Ok(sd) => sd,
                    Err(_) => span_bug!(path.span, "Unexpected path in constructor"),
                };
                // generate fresh inferred sorts for each param
                let fresh_args = (0..sort_def.param_count())
                    .map(|_| self.next_sort_var())
                    .collect_vec();
                let sort_by_name = sort_def.sort_by_field_name(&fresh_args);
                let sort = rty::Sort::App(rty::SortCtor::Adt(sort_def.clone()), fresh_args.into());
                let mut used_fields = FxHashSet::default();
                for expr in *field_exprs {
                    // check each expression against the sort
                    // which will unify inferred variables
                    if let Some(sort) = sort_by_name.get(&expr.ident.name) {
                        self.check_expr(&expr.expr, sort)?;
                    } else {
                        return Err(self.emit_field_not_found(&sort, expr.ident));
                    }
                    if let Some(old_field) = used_fields.replace(expr.ident) {
                        return Err(
                            self.emit_err(errors::DuplicateFieldUsed::new(expr.ident, old_field))
                        );
                    }
                }
                // check the spread against the sort
                if let Some(spread) = spread {
                    self.check_expr(&spread.expr, &sort)?;
                } else if sort_by_name.len() != used_fields.len() {
                    // emit an error because all fields are not used
                    let used_field_names: Vec<rustc_span::Symbol> =
                        used_fields.into_iter().map(|k| k.name).collect();
                    let fields_remaining = sort_by_name
                        .into_keys()
                        .filter(|x| !used_field_names.contains(x))
                        .collect();
                    return Err(self.emit_err(errors::ConstructorMissingFields::new(
                        expr.span,
                        fields_remaining,
                    )));
                }
                Ok(sort)
            }
            _ => Err(self.emit_err(errors::CannotInferSort::new(expr.span))),
        }
    }

    fn synth_var(&mut self, path: &fhir::PathExpr) -> rty::Sort {
        match path.res {
            ExprRes::Param(_, id) => self.param_sort(id),
            ExprRes::Const(def_id) => {
                // TODO(nilehmann) generalize const sorts
                let ty = self.genv.tcx().type_of(def_id).no_bound_vars().unwrap();
                assert!(ty.is_integral());
                rty::Sort::Int
            }
            ExprRes::ConstGeneric(_) => rty::Sort::Int, // TODO: generalize generic-const sorts
            ExprRes::NumConst(_) => rty::Sort::Int,
            ExprRes::GlobalFunc(_, _) => {
                span_bug!(path.span, "unexpected func in var position")
            }
            ExprRes::Struct(_) => {
                span_bug!(path.span, "unexpected struct in var position")
            }
            ExprRes::Enum(_) => {
                span_bug!(path.span, "unexpected enum in var position")
            }
        }
    }

    fn synth_binary_op(
        &mut self,
        expr: &fhir::Expr,
        op: fhir::BinOp,
        e1: &fhir::Expr,
        e2: &fhir::Expr,
    ) -> Result<rty::Sort> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                self.check_expr(e1, &rty::Sort::Bool)?;
                self.check_expr(e2, &rty::Sort::Bool)?;
                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Eq | fhir::BinOp::Ne => {
                let sort = self.next_sort_var();
                self.check_expr(e1, &sort)?;
                self.check_expr(e2, &sort)?;
                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Mod => {
                self.check_expr(e1, &rty::Sort::Int)?;
                self.check_expr(e2, &rty::Sort::Int)?;
                Ok(rty::Sort::Int)
            }
            fhir::BinOp::Lt | fhir::BinOp::Le | fhir::BinOp::Gt | fhir::BinOp::Ge => {
                let sort = self.next_sort_var();
                self.check_expr(e1, &sort)?;
                self.check_expr(e2, &sort)?;

                // Elaborate sort of operator
                let sort = self
                    .fully_resolve(&sort)
                    .map_err(|_| self.emit_err(errors::CannotInferSort::new(expr.span)))?;
                self.wfckresults
                    .bin_rel_sorts_mut()
                    .insert(expr.fhir_id, sort);

                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Add | fhir::BinOp::Sub | fhir::BinOp::Mul | fhir::BinOp::Div => {
                let sort = self.next_num_var();
                self.check_expr(e1, &sort)?;
                self.check_expr(e2, &sort)?;
                Ok(sort)
            }
        }
    }

    fn synth_unary_op(&mut self, op: fhir::UnOp, e: &fhir::Expr) -> Result<rty::Sort> {
        match op {
            fhir::UnOp::Not => {
                self.check_expr(e, &rty::Sort::Bool)?;
                Ok(rty::Sort::Bool)
            }
            fhir::UnOp::Neg => {
                self.check_expr(e, &rty::Sort::Int)?;
                Ok(rty::Sort::Int)
            }
        }
    }

    fn synth_app(
        &mut self,
        func: &fhir::PathExpr,
        args: &[fhir::Expr],
        span: Span,
    ) -> Result<rty::Sort> {
        let fsort = self.synth_func(func)?;
        if args.len() != fsort.inputs().len() {
            return Err(self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("function"),
                fsort.inputs().len(),
                args.len(),
            )));
        }

        iter::zip(args, fsort.inputs())
            .try_for_each_exhaust(|(arg, formal)| self.check_expr(arg, formal))?;

        Ok(fsort.output().clone())
    }

    fn synth_alias_reft_app(
        &mut self,
        fhir_id: FhirId,
        span: Span,
        args: &[fhir::Expr],
    ) -> Result<rty::Sort> {
        let fsort = self.sort_of_alias_reft(fhir_id);
        if args.len() != fsort.inputs().len() {
            return Err(self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("function"),
                fsort.inputs().len(),
                args.len(),
            )));
        }
        iter::zip(args, fsort.inputs())
            .try_for_each_exhaust(|(arg, formal)| self.check_expr(arg, formal))?;

        Ok(fsort.output().clone())
    }

    fn synth_func(&mut self, func: &fhir::PathExpr) -> Result<rty::FuncSort> {
        let poly_fsort = match func.res {
            ExprRes::Param(..) => {
                let sort = self.ensure_resolved_var(func)?;
                let Some(fsort) = self.is_coercible_to_func(&sort, func.fhir_id) else {
                    return Err(self.emit_err(errors::ExpectedFun::new(func.span, &sort)));
                };
                fsort
            }
            ExprRes::GlobalFunc(.., sym) => self.genv.func_decl(sym).emit(&self.genv)?.sort.clone(),
            _ => span_bug!(func.span, "unexpected path in function position"),
        };
        Ok(self.instantiate_func_sort(poly_fsort))
    }

    fn instantiate_func_sort(&mut self, fsort: rty::PolyFuncSort) -> rty::FuncSort {
        let args = fsort
            .params()
            .map(|kind| {
                match kind {
                    rty::SortParamKind::Sort => rty::SortArg::Sort(self.next_sort_var()),
                    rty::SortParamKind::BvSize => rty::SortArg::BvSize(self.next_bv_size_var()),
                }
            })
            .collect_vec();
        fsort.instantiate(&args)
    }

    pub(crate) fn insert_sort_for_bty(&mut self, fhir_id: FhirId, sort: rty::Sort) {
        self.sort_of_bty.insert(fhir_id, sort);
    }

    pub(crate) fn sort_of_bty(&self, fhir_id: FhirId) -> rty::Sort {
        self.sort_of_bty
            .get(&fhir_id)
            .unwrap_or_else(|| tracked_span_bug!("no entry found for `{fhir_id:?}`"))
            .clone()
    }

    pub(crate) fn insert_sort_for_alias_reft(&mut self, fhir_id: FhirId, fsort: rty::FuncSort) {
        self.sort_of_alias_reft.insert(fhir_id, fsort);
    }

    fn sort_of_alias_reft(&self, fhir_id: FhirId) -> rty::FuncSort {
        self.sort_of_alias_reft
            .get(&fhir_id)
            .unwrap_or_else(|| tracked_span_bug!("no entry found for `{fhir_id:?}`"))
            .clone()
    }

    // FIXME(nilehmann) this assumes weak aliases appear shallowly and are only created for the
    // sorts associated to base types. We should find a more robust way to do normalization for
    // sort checking. Once we do that we can also stop expanding self aliases in `conv::conv_sort`.
    pub(crate) fn normalize_weak_alias_sorts(&mut self) -> QueryResult {
        for sort in self.sort_of_bty.values_mut() {
            if let rty::Sort::Alias(rty::AliasKind::Weak, alias_ty) = sort {
                *sort = self.genv.normalize_weak_alias_sort(alias_ty)?;
            }
        }
        Ok(())
    }
}

impl<'genv> InferCtxt<'genv, '_> {
    /// Push a layer of binders. We assume all names are fresh so we don't care about shadowing
    pub(super) fn insert_params(&mut self, params: &[fhir::RefineParam]) -> Result {
        for param in params {
            let sort = conv::conv_sort(self.genv, &param.sort, &mut || self.next_sort_var())
                .emit(&self.genv)?;
            self.insert_param(param.id, sort, param.kind);
        }
        Ok(())
    }

    pub(super) fn insert_param(
        &mut self,
        id: fhir::ParamId,
        sort: rty::Sort,
        kind: fhir::ParamKind,
    ) {
        self.params.insert(id, (sort, kind));
    }

    /// Whether a value of `sort1` can be automatically coerced to a value of `sort2`. A value of an
    /// [`rty::SortCtor::Adt`] sort with a single field of sort `s` can be coerced to a value of sort
    /// `s` and vice versa, i.e., we can automatically project the field out of the record or inject
    /// a value into a record.
    fn is_coercible(&mut self, sort1: &rty::Sort, sort2: &rty::Sort, fhir_id: FhirId) -> bool {
        if self.try_equate(sort1, sort2).is_some() {
            return true;
        }

        let mut sort1 = sort1.clone();
        let mut sort2 = sort2.clone();

        let mut coercions = vec![];
        if let Some((def_id, sort)) = self.is_single_field_record(&sort1) {
            coercions.push(rty::Coercion::Project(def_id));
            sort1 = sort.clone();
        }
        if let Some((def_id, sort)) = self.is_single_field_record(&sort2) {
            coercions.push(rty::Coercion::Inject(def_id));
            sort2 = sort.clone();
        }
        self.wfckresults.coercions_mut().insert(fhir_id, coercions);
        self.try_equate(&sort1, &sort2).is_some()
    }

    fn is_coercible_from_func(
        &mut self,
        sort: &rty::Sort,
        fhir_id: FhirId,
    ) -> Option<rty::PolyFuncSort> {
        if let rty::Sort::Func(fsort) = sort {
            Some(fsort.clone())
        } else if let Some((def_id, rty::Sort::Func(fsort))) = self.is_single_field_record(sort) {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![rty::Coercion::Inject(def_id)]);
            Some(fsort.clone())
        } else {
            None
        }
    }

    fn is_coercible_to_func(
        &mut self,
        sort: &rty::Sort,
        fhir_id: FhirId,
    ) -> Option<rty::PolyFuncSort> {
        if let rty::Sort::Func(fsort) = sort {
            Some(fsort.clone())
        } else if let Some((def_id, rty::Sort::Func(fsort))) = self.is_single_field_record(sort) {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![rty::Coercion::Project(def_id)]);
            Some(fsort.clone())
        } else {
            None
        }
    }

    fn try_equate(&mut self, sort1: &rty::Sort, sort2: &rty::Sort) -> Option<rty::Sort> {
        let sort1 = self.resolve_vars_if_possible(sort1);
        let sort2 = self.resolve_vars_if_possible(sort2);
        self.try_equate_inner(&sort1, &sort2)
    }

    fn try_equate_inner(&mut self, sort1: &rty::Sort, sort2: &rty::Sort) -> Option<rty::Sort> {
        match (sort1, sort2) {
            (rty::Sort::Infer(rty::SortVar(vid1)), rty::Sort::Infer(rty::SortVar(vid2))) => {
                self.sort_unification_table
                    .unify_var_var(*vid1, *vid2)
                    .ok()?;
            }
            (rty::Sort::Infer(rty::SortVar(vid)), sort)
            | (sort, rty::Sort::Infer(rty::SortVar(vid))) => {
                self.sort_unification_table
                    .unify_var_value(*vid, Some(sort.clone()))
                    .ok()?;
            }
            (rty::Sort::Infer(rty::NumVar(vid1)), rty::Sort::Infer(rty::NumVar(vid2))) => {
                self.num_unification_table
                    .unify_var_var(*vid1, *vid2)
                    .ok()?;
            }
            (rty::Sort::Infer(rty::NumVar(vid)), rty::Sort::Int)
            | (rty::Sort::Int, rty::Sort::Infer(rty::NumVar(vid))) => {
                self.num_unification_table
                    .unify_var_value(*vid, Some(rty::NumVarValue::Int))
                    .ok()?;
            }
            (rty::Sort::Infer(rty::NumVar(vid)), rty::Sort::Real)
            | (rty::Sort::Real, rty::Sort::Infer(rty::NumVar(vid))) => {
                self.num_unification_table
                    .unify_var_value(*vid, Some(rty::NumVarValue::Real))
                    .ok()?;
            }
            (rty::Sort::App(ctor1, args1), rty::Sort::App(ctor2, args2)) => {
                if ctor1 != ctor2 || args1.len() != args2.len() {
                    return None;
                }
                let mut args = vec![];
                for (s1, s2) in args1.iter().zip(args2.iter()) {
                    args.push(self.try_equate_inner(s1, s2)?);
                }
            }
            (rty::Sort::BitVec(size1), rty::Sort::BitVec(size2)) => {
                self.try_equate_bv_sizes(*size1, *size2)?;
            }
            _ if sort1 == sort2 => {}
            _ => return None,
        }
        Some(sort1.clone())
    }

    fn try_equate_bv_sizes(
        &mut self,
        size1: rty::BvSize,
        size2: rty::BvSize,
    ) -> Option<rty::BvSize> {
        match (size1, size2) {
            (rty::BvSize::Infer(vid1), rty::BvSize::Infer(vid2)) => {
                self.bv_size_unification_table
                    .unify_var_var(vid1, vid2)
                    .ok()?;
            }
            (rty::BvSize::Infer(vid), size) | (size, rty::BvSize::Infer(vid)) => {
                self.bv_size_unification_table
                    .unify_var_value(vid, Some(size))
                    .ok()?;
            }
            _ if size1 == size2 => {}
            _ => return None,
        }
        Some(size1)
    }

    fn equate(&mut self, sort1: &rty::Sort, sort2: &rty::Sort) -> rty::Sort {
        self.try_equate(sort1, sort2)
            .unwrap_or_else(|| bug!("failed to equate sorts: `{sort1:?}` `{sort2:?}`"))
    }

    pub(crate) fn next_sort_var(&mut self) -> rty::Sort {
        rty::Sort::Infer(rty::SortVar(self.next_sort_vid()))
    }

    fn next_num_var(&mut self) -> rty::Sort {
        rty::Sort::Infer(rty::NumVar(self.next_num_vid()))
    }

    fn next_sort_vid(&mut self) -> rty::SortVid {
        self.sort_unification_table.new_key(None)
    }

    fn next_num_vid(&mut self) -> rty::NumVid {
        self.num_unification_table.new_key(None)
    }

    fn next_bv_size_var(&mut self) -> rty::BvSize {
        rty::BvSize::Infer(self.next_bv_size_vid())
    }

    fn next_bv_size_vid(&mut self) -> rty::BvSizeVid {
        self.bv_size_unification_table.new_key(None)
    }

    pub(crate) fn resolve_param_sort(&mut self, param: &fhir::RefineParam) -> Result {
        let sort = self.param_sort(param.id);
        match self.fully_resolve(&sort) {
            Ok(sort) => {
                self.wfckresults
                    .node_sorts_mut()
                    .insert(param.fhir_id, sort);
                Ok(())
            }
            Err(_) => Err(self.emit_err(errors::SortAnnotationNeeded::new(param))),
        }
    }

    fn ensure_resolved_var(&mut self, path: &fhir::PathExpr) -> Result<rty::Sort> {
        let ExprRes::Param(_, id) = path.res else { span_bug!(path.span, "unexpected path") };
        let sort = self.param_sort(id);
        self.fully_resolve(&sort)
            .map_err(|_| self.emit_err(errors::CannotInferSort::new(path.span)))
    }

    fn is_single_field_record(&mut self, sort: &rty::Sort) -> Option<(DefId, rty::Sort)> {
        if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = sort
            && let [sort] = &sort_def.field_sorts(sort_args)[..]
        {
            Some((sort_def.did(), sort.clone()))
        } else {
            None
        }
    }

    pub(crate) fn into_results(self) -> WfckResults {
        self.wfckresults
    }

    pub(crate) fn infer_mode(&self, id: fhir::ParamId) -> fhir::InferMode {
        fhir::InferMode::from_param_kind(self.params[&id].1)
    }

    #[track_caller]
    pub(crate) fn param_sort(&self, id: fhir::ParamId) -> rty::Sort {
        self.params
            .get(&id)
            .unwrap_or_else(|| bug!("no entry found for `{id:?}`"))
            .0
            .clone()
    }

    fn shallow_resolve(&mut self, sort: &rty::Sort) -> rty::Sort {
        sort.fold_with(&mut ShallowResolver { infcx: self })
    }

    fn resolve_vars_if_possible(&mut self, sort: &rty::Sort) -> rty::Sort {
        sort.fold_with(&mut OpportunisticResolver { infcx: self })
    }

    pub(crate) fn fully_resolve(&mut self, sort: &rty::Sort) -> std::result::Result<rty::Sort, ()> {
        sort.try_fold_with(&mut FullResolver { infcx: self })
    }
}

pub(crate) struct ImplicitParamInferer<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> ImplicitParamInferer<'a, 'genv, 'tcx> {
    pub(crate) fn infer(infcx: &'a mut InferCtxt<'genv, 'tcx>, node: &fhir::Node<'genv>) -> Result {
        let errors = Errors::new(infcx.genv.sess());
        let mut vis = Self { infcx, errors };
        vis.visit_node(node);
        vis.errors.into_result()
    }

    fn infer_implicit_params(&mut self, idx: &fhir::Expr, expected: &rty::Sort) {
        match idx.kind {
            fhir::ExprKind::Var(var, Some(_)) => {
                let (_, id) = var.res.expect_param();
                let found = self.infcx.param_sort(id);
                self.infcx.equate(&found, expected);
            }
            fhir::ExprKind::Record(flds) => {
                if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = expected {
                    let sorts = sort_def.field_sorts(sort_args);
                    if flds.len() != sorts.len() {
                        self.errors.emit(errors::ArgCountMismatch::new(
                            Some(idx.span),
                            String::from("type"),
                            sorts.len(),
                            flds.len(),
                        ));
                        return;
                    }
                    for (f, sort) in iter::zip(flds, &sorts) {
                        self.infer_implicit_params(f, sort);
                    }
                } else {
                    self.errors.emit(errors::ArgCountMismatch::new(
                        Some(idx.span),
                        String::from("type"),
                        1,
                        flds.len(),
                    ));
                }
            }
            _ => {}
        }
    }
}

impl<'genv> fhir::visit::Visitor<'genv> for ImplicitParamInferer<'_, 'genv, '_> {
    fn visit_ty(&mut self, ty: &fhir::Ty<'genv>) {
        if let fhir::TyKind::Indexed(bty, idx) = &ty.kind {
            let expected = self.infcx.sort_of_bty(bty.fhir_id);
            self.infer_implicit_params(idx, &expected);
        }
        fhir::visit::walk_ty(self, ty);
    }
}

impl InferCtxt<'_, '_> {
    #[track_caller]
    fn emit_sort_mismatch(
        &mut self,
        span: Span,
        expected: &rty::Sort,
        found: &rty::Sort,
    ) -> ErrorGuaranteed {
        let expected = self.resolve_vars_if_possible(expected);
        let found = self.resolve_vars_if_possible(found);
        self.emit_err(errors::SortMismatch::new(span, expected, found))
    }

    fn emit_field_not_found(&mut self, sort: &rty::Sort, field: Ident) -> ErrorGuaranteed {
        self.emit_err(errors::FieldNotFound::new(sort.clone(), field))
    }

    #[track_caller]
    fn emit_err<'b>(&'b self, err: impl Diagnostic<'b>) -> ErrorGuaranteed {
        self.genv.sess().emit_err(err)
    }
}

fn synth_lit(lit: fhir::Lit) -> rty::Sort {
    match lit {
        fhir::Lit::Int(_) => rty::Sort::Int,
        fhir::Lit::Bool(_) => rty::Sort::Bool,
        fhir::Lit::Real(_) => rty::Sort::Real,
        fhir::Lit::Str(_) => rty::Sort::Str,
        fhir::Lit::Char(_) => rty::Sort::Char,
    }
}

struct ShallowResolver<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
}

impl TypeFolder for ShallowResolver<'_, '_, '_> {
    fn fold_sort(&mut self, sort: &rty::Sort) -> rty::Sort {
        match sort {
            rty::Sort::Infer(rty::SortVar(vid)) => {
                // if `sort` is a sort variable, it can be resolved to an num/bit-vec variable,
                // which can then be recursively resolved, hence the recursion. Note though that
                // we prevent sort variables from unifying to other sort variables directly (though
                // they may be embedded structurally), so this recursion should always be of very
                // limited depth.
                self.infcx
                    .sort_unification_table
                    .probe_value(*vid)
                    .map(|sort| sort.fold_with(self))
                    .unwrap_or(sort.clone())
            }
            rty::Sort::Infer(rty::NumVar(vid)) => {
                self.infcx
                    .num_unification_table
                    .probe_value(*vid)
                    .map(rty::NumVarValue::to_sort)
                    .unwrap_or(sort.clone())
            }
            rty::Sort::BitVec(rty::BvSize::Infer(vid)) => {
                self.infcx
                    .bv_size_unification_table
                    .probe_value(*vid)
                    .map(rty::Sort::BitVec)
                    .unwrap_or(sort.clone())
            }
            _ => sort.clone(),
        }
    }
}

struct OpportunisticResolver<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
}

impl TypeFolder for OpportunisticResolver<'_, '_, '_> {
    fn fold_sort(&mut self, sort: &rty::Sort) -> rty::Sort {
        let s = self.infcx.shallow_resolve(sort);
        s.super_fold_with(self)
    }
}

struct FullResolver<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
}

impl FallibleTypeFolder for FullResolver<'_, '_, '_> {
    type Error = ();

    fn try_fold_sort(&mut self, sort: &rty::Sort) -> std::result::Result<rty::Sort, Self::Error> {
        let s = self.infcx.shallow_resolve(sort);
        match s {
            rty::Sort::Infer(_) => Err(()),
            _ => s.try_super_fold_with(self),
        }
    }
}
