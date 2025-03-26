use std::iter;

use ena::unify::InPlaceUnificationTable;
use flux_common::{bug, iter::IterExt, result::ResultExt, span_bug, tracked_span_bug};
use flux_errors::{ErrorGuaranteed, Errors};
use flux_middle::{
    THEORY_FUNCS,
    fhir::{self, ExprRes, FhirId, FluxOwnerId, SpecFuncKind, visit::Visitor as _},
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::{
        self, AdtSortDef, FuncSort, WfckResults,
        fold::{FallibleTypeFolder, TypeFoldable, TypeFolder, TypeSuperFoldable},
    },
};
use itertools::{Itertools, izip};
use rustc_data_structures::unord::UnordMap;
use rustc_errors::Diagnostic;
use rustc_hash::FxHashMap;
use rustc_span::{Span, def_id::DefId, symbol::Ident};

use super::errors;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(super) struct InferCtxt<'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    pub wfckresults: WfckResults,
    sort_unification_table: InPlaceUnificationTable<rty::SortVid>,
    num_unification_table: InPlaceUnificationTable<rty::NumVid>,
    bv_size_unification_table: InPlaceUnificationTable<rty::BvSizeVid>,
    params: FxHashMap<fhir::ParamId, (fhir::RefineParam<'genv>, rty::Sort)>,
    sort_of_bty: FxHashMap<FhirId, rty::Sort>,
    sort_of_literal: FxHashMap<FhirId, (rty::Sort, Span)>,
    sort_of_bin_op: FxHashMap<FhirId, (rty::Sort, Span)>,
    path_args: UnordMap<FhirId, rty::GenericArgs>,
    sort_of_alias_reft: FxHashMap<FhirId, rty::FuncSort>,
}

impl<'genv, 'tcx> InferCtxt<'genv, 'tcx> {
    pub(super) fn new(genv: GlobalEnv<'genv, 'tcx>, owner: FluxOwnerId) -> Self {
        // We skip 0 because that's used for sort dummy self types during conv.
        let mut sort_unification_table = InPlaceUnificationTable::new();
        sort_unification_table.new_key(None);
        Self {
            genv,
            wfckresults: WfckResults::new(owner),
            sort_unification_table,
            num_unification_table: InPlaceUnificationTable::new(),
            bv_size_unification_table: InPlaceUnificationTable::new(),
            params: Default::default(),
            sort_of_bty: Default::default(),
            sort_of_literal: Default::default(),
            sort_of_bin_op: Default::default(),
            path_args: Default::default(),
            sort_of_alias_reft: Default::default(),
        }
    }

    fn check_abs(
        &mut self,
        expr: &fhir::Expr,
        params: &[fhir::RefineParam],
        body: &fhir::Expr,
        expected: &rty::Sort,
    ) -> Result {
        let Some(fsort) = self.is_coercible_from_func(expected, expr.fhir_id) else {
            return Err(self.emit_err(errors::UnexpectedFun::new(expr.span, expected)));
        };

        let fsort = fsort.expect_mono();

        if params.len() != fsort.inputs().len() {
            return Err(self.emit_err(errors::ParamCountMismatch::new(
                expr.span,
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
            .insert(body.fhir_id, fsort.output().clone());
        Ok(())
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
        let sort_by_field_name = sort_def.struct_variant().sort_by_field_name(sort_args);
        let mut used_fields = FxHashMap::default();
        for expr in field_exprs {
            // make sure that the field is actually a field
            let Some(sort) = sort_by_field_name.get(&expr.ident.name) else {
                return Err(self.emit_err(errors::FieldNotFound::new(expected.clone(), expr.ident)));
            };
            if let Some(old_field) = used_fields.insert(expr.ident.name, expr.ident) {
                return Err(self.emit_err(errors::DuplicateFieldUsed::new(expr.ident, old_field)));
            }
            self.check_expr(&expr.expr, sort)?;
        }
        if let Some(spread) = spread {
            // must check that the spread is of the same sort as the constructor
            self.check_expr(&spread.expr, expected)
        } else if sort_by_field_name.len() != used_fields.len() {
            // emit an error because all fields are not used
            let missing_fields = sort_by_field_name
                .into_keys()
                .filter(|x| !used_fields.contains_key(x))
                .collect();
            Err(self.emit_err(errors::ConstructorMissingFields::new(expr_span, missing_fields)))
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
            let sorts = sort_def.struct_variant().field_sorts(sort_args);
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
            fhir::ExprKind::Abs(params, body) => {
                self.check_abs(expr, params, body, expected)?;
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
            | fhir::ExprKind::BoundedQuant(..)
            | fhir::ExprKind::Constructor(..) => {
                let found = self.synth_expr(expr)?;
                let found = self.resolve_vars_if_possible(&found);
                let expected = self.resolve_vars_if_possible(expected);
                if !self.is_coercible(&found, &expected, expr.fhir_id) {
                    return Err(self.emit_sort_mismatch(expr.span, &expected, &found));
                }
            }
            fhir::ExprKind::Err(_) => {
                // an error has already been reported so we can just skip
            }
        }
        Ok(())
    }

    pub(super) fn check_loc(&mut self, loc: &fhir::PathExpr) -> Result {
        let found = self.synth_path(loc)?;
        if found == rty::Sort::Loc {
            Ok(())
        } else {
            Err(self.emit_sort_mismatch(loc.span, &rty::Sort::Loc, &found))
        }
    }

    fn synth_lit(&mut self, lit: fhir::Lit, expr: &fhir::Expr) -> rty::Sort {
        match lit {
            fhir::Lit::Int(_) => {
                let sort = self.next_num_var();
                self.sort_of_literal
                    .insert(expr.fhir_id, (sort.clone(), expr.span));
                sort
            }
            fhir::Lit::Bool(_) => rty::Sort::Bool,
            fhir::Lit::Real(_) => rty::Sort::Real,
            fhir::Lit::Str(_) => rty::Sort::Str,
            fhir::Lit::Char(_) => rty::Sort::Char,
        }
    }

    fn synth_expr(&mut self, expr: &fhir::Expr) -> Result<rty::Sort> {
        match &expr.kind {
            fhir::ExprKind::Var(var, _) => self.synth_path(var),
            fhir::ExprKind::Literal(lit) => Ok(self.synth_lit(*lit, expr)),
            fhir::ExprKind::BinaryOp(op, e1, e2) => self.synth_binary_op(expr, *op, e1, e2),
            fhir::ExprKind::UnaryOp(op, e) => self.synth_unary_op(*op, e),
            fhir::ExprKind::App(callee, args) => {
                let sort = self.ensure_resolved_path(callee)?;
                let Some(poly_fsort) = self.is_coercible_to_func(&sort, callee.fhir_id) else {
                    return Err(self.emit_err(errors::ExpectedFun::new(callee.span, &sort)));
                };
                let fsort = self.instantiate_func_sort(poly_fsort);
                self.synth_app(fsort, args, expr.span)
            }
            fhir::ExprKind::BoundedQuant(.., body) => {
                self.check_expr(body, &rty::Sort::Bool)?;
                Ok(rty::Sort::Bool)
            }
            fhir::ExprKind::Alias(_alias_reft, args) => {
                // To check the application we only need the sort of `_alias_reft` which we collected
                // during early conv, but should we do any extra checks on `_alias_reft`?
                let fsort = self.sort_of_alias_reft(expr.fhir_id);
                self.synth_app(fsort, args, expr.span)
            }
            fhir::ExprKind::IfThenElse(p, e1, e2) => {
                self.check_expr(p, &rty::Sort::Bool)?;
                let sort = self.synth_expr(e1)?;
                self.check_expr(e2, &sort)?;
                Ok(sort)
            }
            fhir::ExprKind::Dot(var, fld) => {
                let sort = self.ensure_resolved_path(var)?;
                match &sort {
                    rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) => {
                        let (proj, sort) = sort_def
                            .struct_variant()
                            .field_by_name(sort_def.did(), sort_args, fld.name)
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
                    ExprRes::Ctor(def_id) => def_id,
                    _ => span_bug!(expr.span, "unexpected path in constructor"),
                };
                let sort_def = self
                    .genv
                    .adt_sort_def_of(path_def_id)
                    .map_err(|e| self.emit_err(e))?;
                // generate fresh inferred sorts for each param
                let fresh_args: rty::List<_> = (0..sort_def.param_count())
                    .map(|_| self.next_sort_var())
                    .collect();
                let sort = rty::Sort::App(rty::SortCtor::Adt(sort_def.clone()), fresh_args.clone());
                // check fields & spread against fresh args
                self.check_field_exprs(
                    expr.span,
                    &sort_def,
                    &fresh_args,
                    field_exprs,
                    spread,
                    &sort,
                )?;
                Ok(sort)
            }
            _ => Err(self.emit_err(errors::CannotInferSort::new(expr.span))),
        }
    }

    fn synth_path(&mut self, path: &fhir::PathExpr) -> Result<rty::Sort> {
        match path.res {
            ExprRes::Param(_, id) => Ok(self.param_sort(id)),
            ExprRes::Const(def_id) => {
                if let Some(sort) = self.genv.sort_of_def_id(def_id).emit(&self.genv)? {
                    let info = self.genv.constant_info(def_id).emit(&self.genv)?;
                    // non-integral constant
                    if sort != rty::Sort::Int && matches!(info, rty::ConstantInfo::Uninterpreted) {
                        Err(self.emit_err(errors::ConstantAnnotationNeeded::new(path.span)))?;
                    }
                    Ok(sort)
                } else {
                    span_bug!(path.span, "unexpected const")
                }
            }
            ExprRes::Variant(def_id) => {
                let Some(sort) = self.genv.sort_of_def_id(def_id).emit(&self.genv)? else {
                    span_bug!(path.span, "unexpected variant {def_id:?}")
                };
                Ok(sort)
            }
            ExprRes::ConstGeneric(_) => Ok(rty::Sort::Int), // TODO: generalize generic-const sorts
            ExprRes::NumConst(_) => Ok(rty::Sort::Int),
            ExprRes::GlobalFunc(SpecFuncKind::Def(name) | SpecFuncKind::Uif(name)) => {
                Ok(rty::Sort::Func(self.genv.func_sort(name).emit(&self.genv)?))
            }
            ExprRes::GlobalFunc(SpecFuncKind::Thy(itf)) => {
                Ok(rty::Sort::Func(THEORY_FUNCS.get(&itf).unwrap().sort.clone()))
            }
            ExprRes::Ctor(_) => {
                span_bug!(path.span, "unexpected constructor in var position")
            }
        }
    }

    fn check_integral(&mut self, op: fhir::BinOp, sort: &rty::Sort, span: Span) -> Result {
        if matches!(op, fhir::BinOp::Mod) {
            let sort = self
                .fully_resolve(sort)
                .map_err(|_| self.emit_err(errors::CannotInferSort::new(span)))?;
            if !matches!(sort, rty::Sort::Int | rty::Sort::BitVec(_)) {
                span_bug!(span, "unexpected sort {sort:?} for operator {op:?}");
            }
        }
        Ok(())
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
            fhir::BinOp::Lt | fhir::BinOp::Le | fhir::BinOp::Gt | fhir::BinOp::Ge => {
                let sort = self.next_sort_var();
                self.check_expr(e1, &sort)?;
                self.check_expr(e2, &sort)?;
                self.sort_of_bin_op
                    .insert(expr.fhir_id, (sort.clone(), expr.span));
                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Add
            | fhir::BinOp::Sub
            | fhir::BinOp::Mul
            | fhir::BinOp::Div
            | fhir::BinOp::Mod => {
                let sort = self.next_num_var();
                self.check_expr(e1, &sort)?;
                self.check_expr(e2, &sort)?;
                self.sort_of_bin_op
                    .insert(expr.fhir_id, (sort.clone(), expr.span));
                // check that the sort is integral for mod
                self.check_integral(op, &sort, expr.span)?;

                Ok(sort)
            }
            fhir::BinOp::BitAnd
            | fhir::BinOp::BitOr
            | fhir::BinOp::BitShl
            | fhir::BinOp::BitShr => {
                let sort = rty::Sort::BitVec(self.next_bv_size_var());
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

    fn synth_app(&mut self, fsort: FuncSort, args: &[fhir::Expr], span: Span) -> Result<rty::Sort> {
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

    pub(crate) fn insert_path_args(&mut self, fhir_id: FhirId, args: rty::GenericArgs) {
        self.path_args.insert(fhir_id, args);
    }

    pub(crate) fn path_args(&self, fhir_id: FhirId) -> rty::GenericArgs {
        self.path_args
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

    // FIXME(nilehmann) this is a bit of a hack. We should find a more robust way to do normalization
    // for sort checking, including normalizing projections. Maybe we can do lazy normalization. Once
    // we do that maybe we can also stop expanding aliases in `ConvCtxt::conv_sort`.
    pub(crate) fn normalize_weak_alias_sorts(&mut self) -> QueryResult {
        for sort in self.sort_of_bty.values_mut() {
            *sort = self.genv.deep_normalize_weak_alias_sorts(sort)?;
        }
        for fsort in self.sort_of_alias_reft.values_mut() {
            *fsort = self.genv.deep_normalize_weak_alias_sorts(fsort)?;
        }
        Ok(())
    }
}

impl<'genv> InferCtxt<'genv, '_> {
    pub(super) fn declare_param(&mut self, param: fhir::RefineParam<'genv>, sort: rty::Sort) {
        self.params.insert(param.id, (param, sort));
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
        if let Some((def_id, sort)) = self.is_single_field_struct(&sort1) {
            coercions.push(rty::Coercion::Project(def_id));
            sort1 = sort.clone();
        }
        if let Some((def_id, sort)) = self.is_single_field_struct(&sort2) {
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
        } else if let Some((def_id, rty::Sort::Func(fsort))) = self.is_single_field_struct(sort) {
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
        } else if let Some((def_id, rty::Sort::Func(fsort))) = self.is_single_field_struct(sort) {
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
            (rty::Sort::Infer(rty::NumVar(vid)), rty::Sort::BitVec(sz))
            | (rty::Sort::BitVec(sz), rty::Sort::Infer(rty::NumVar(vid))) => {
                self.num_unification_table
                    .unify_var_value(*vid, Some(rty::NumVarValue::BitVec(*sz)))
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

    pub(crate) fn next_sort_vid(&mut self) -> rty::SortVid {
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

    fn ensure_resolved_path(&mut self, path: &fhir::PathExpr) -> Result<rty::Sort> {
        let sort = self.synth_path(path)?;
        self.fully_resolve(&sort)
            .map_err(|_| self.emit_err(errors::CannotInferSort::new(path.span)))
    }

    fn is_single_field_struct(&mut self, sort: &rty::Sort) -> Option<(DefId, rty::Sort)> {
        if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = sort
            && let Some(variant) = sort_def.opt_struct_variant()
            && let [sort] = &variant.field_sorts(sort_args)[..]
        {
            Some((sort_def.did(), sort.clone()))
        } else {
            None
        }
    }

    pub(crate) fn into_results(mut self) -> Result<WfckResults> {
        // Make sure the int literals are fully resolved
        for (fhir_id, (sort, span)) in std::mem::take(&mut self.sort_of_literal) {
            let sort = self
                .fully_resolve(&sort)
                .map_err(|_| self.emit_err(errors::CannotInferSort::new(span)))?;
            self.wfckresults.node_sorts_mut().insert(fhir_id, sort);
        }

        // Make sure the binary operators are fully resolved
        for (fhir_id, (sort, span)) in std::mem::take(&mut self.sort_of_bin_op) {
            let sort = self
                .fully_resolve(&sort)
                .map_err(|_| self.emit_err(errors::CannotInferSort::new(span)))?;
            self.wfckresults.bin_op_sorts_mut().insert(fhir_id, sort);
        }

        // Make sure all parameters are fully resolved
        for (_, (param, sort)) in std::mem::take(&mut self.params) {
            let sort = self
                .fully_resolve(&sort)
                .map_err(|_| self.emit_err(errors::SortAnnotationNeeded::new(&param)))?;
            self.wfckresults
                .node_sorts_mut()
                .insert(param.fhir_id, sort);
        }

        Ok(self.wfckresults)
    }

    pub(crate) fn infer_mode(&self, id: fhir::ParamId) -> fhir::InferMode {
        fhir::InferMode::from_param_kind(self.params[&id].0.kind)
    }

    #[track_caller]
    pub(crate) fn param_sort(&self, id: fhir::ParamId) -> rty::Sort {
        self.params
            .get(&id)
            .unwrap_or_else(|| bug!("no entry found for `{id:?}`"))
            .1
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

/// Before the main sort inference, we do a first traversal checking all implicitly scoped parameters
/// declared wih `@` or `#` and infer their sort based on the type they are indexing, e.g., if `n` was
/// declared as `i32[@n]`, we infer `int` for `n`.
///
/// This prepass is necessary because sometimes the order in which we traverse expressions can
/// affect what we can infer. By resolving implicit parameters first, we ensure more consistent and
/// complete inference regardless of how expressions are later traversed.
///
/// It should be possible to improve sort checking (e.g., by allowing partially resolved sorts in
/// function position) such that we don't need this anymore.
pub(crate) struct ImplicitParamInferer<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> ImplicitParamInferer<'a, 'genv, 'tcx> {
    pub(crate) fn infer(
        infcx: &'a mut InferCtxt<'genv, 'tcx>,
        node: &fhir::OwnerNode<'genv>,
    ) -> Result {
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
                    let sorts = sort_def.struct_variant().field_sorts(sort_args);
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
