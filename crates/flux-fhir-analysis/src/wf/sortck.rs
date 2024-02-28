use std::iter;

use ena::unify::InPlaceUnificationTable;
use flux_common::{bug, iter::IterExt, span_bug};
use flux_errors::{ErrorGuaranteed, Errors};
use flux_middle::{
    fhir::{self, visit::Visitor as _, ExprRes, FhirId, FluxOwnerId},
    global_env::GlobalEnv,
    pretty,
    rty::{
        self,
        fold::{FallibleTypeFolder, TypeFoldable, TypeFolder, TypeSuperFoldable},
        WfckResults,
    },
};
use itertools::izip;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::IntoDiagnostic;
use rustc_span::{def_id::DefId, Span};

use super::errors;
use crate::{compare_impl_item::errors::InvalidAssocReft, conv};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(super) struct InferCtxt<'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    params: UnordMap<fhir::ParamId, (rty::Sort, fhir::ParamKind)>,
    pub(super) sort_unification_table: InPlaceUnificationTable<rty::SortVid>,
    num_unification_table: InPlaceUnificationTable<rty::NumVid>,
    pub wfckresults: WfckResults<'genv>,
}

impl<'genv, 'tcx> InferCtxt<'genv, 'tcx> {
    pub(super) fn new(genv: GlobalEnv<'genv, 'tcx>, owner: FluxOwnerId) -> Self {
        Self {
            genv,
            wfckresults: WfckResults::new(owner),
            sort_unification_table: InPlaceUnificationTable::new(),
            num_unification_table: InPlaceUnificationTable::new(),
            params: Default::default(),
        }
    }

    pub(super) fn check_refine_arg(
        &mut self,
        arg: &fhir::RefineArg,
        expected: &rty::Sort,
    ) -> Result {
        match &arg.kind {
            fhir::RefineArgKind::Expr(expr) => self.check_expr(expr, expected),
            fhir::RefineArgKind::Abs(params, body) => self.check_abs(arg, params, body, expected),
            fhir::RefineArgKind::Record(flds) => self.check_record(arg, flds, expected),
        }
    }

    fn check_abs(
        &mut self,
        arg: &fhir::RefineArg,
        params: &[fhir::RefineParam],
        body: &fhir::Expr,
        expected: &rty::Sort,
    ) -> Result {
        if let Some(fsort) = self.is_coercible_from_func(expected, arg.fhir_id) {
            let fsort = fsort.expect_mono();
            self.insert_params(params);

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

    fn check_record(
        &mut self,
        arg: &fhir::RefineArg,
        flds: &[fhir::RefineArg],
        expected: &rty::Sort,
    ) -> Result {
        if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = expected {
            let sorts = sort_def.sorts(sort_args);
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
                .map(|(arg, expected)| self.check_refine_arg(arg, expected))
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
            fhir::ExprKind::UnaryOp(..)
            | fhir::ExprKind::BinaryOp(..)
            | fhir::ExprKind::Dot(..)
            | fhir::ExprKind::App(..)
            | fhir::ExprKind::Alias(..)
            | fhir::ExprKind::Var(..)
            | fhir::ExprKind::Literal(..) => {
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
            fhir::ExprKind::Alias(alias, func_args) => {
                self.synth_alias_reft_app(alias, func_args, expr.span)
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
                        sort_def
                            .field_sort(sort_args, fld.name)
                            .ok_or_else(|| self.emit_field_not_found(&sort, *fld))
                    }
                    rty::Sort::Bool | rty::Sort::Int | rty::Sort::Real => {
                        Err(self.emit_err(errors::InvalidPrimitiveDotAccess::new(&sort, *fld)))
                    }
                    _ => Err(self.emit_field_not_found(&sort, *fld)),
                }
            }
        }
    }

    fn synth_var(&mut self, path: &fhir::PathExpr) -> rty::Sort {
        match path.res {
            ExprRes::Param(_, id) => self.param_sort(id),
            ExprRes::Const(_) => rty::Sort::Int, // TODO: generalize const sorts
            ExprRes::NumConst(_) => rty::Sort::Int,
            ExprRes::GlobalFunc(_, _) => {
                span_bug!(path.span, "unexpected func in var position")
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
        alias: &fhir::AliasReft,
        args: &[fhir::Expr],
        span: Span,
    ) -> Result<rty::Sort> {
        let Some(fsort) = self.genv.sort_of_alias_reft(alias) else {
            return Err(self.emit_err(InvalidAssocReft::new(
                span,
                alias.name,
                pretty::def_id_to_string(alias.trait_id),
            )));
        };
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
            ExprRes::GlobalFunc(.., sym) => self.genv.func_decl(sym).sort.clone(),
            _ => span_bug!(func.span, "unexpected path in function position"),
        };
        Ok(self.instantiate_func_sort(poly_fsort))
    }

    fn instantiate_func_sort(&mut self, fsort: rty::PolyFuncSort) -> rty::FuncSort {
        let args: Vec<rty::Sort> = std::iter::repeat_with(|| self.next_sort_var())
            .take(fsort.params)
            .collect();
        fsort.instantiate(&args)
    }
}

impl<'genv> InferCtxt<'genv, '_> {
    /// Push a layer of binders. We assume all names are fresh so we don't care about shadowing
    pub(super) fn insert_params(&mut self, params: &[fhir::RefineParam]) {
        for param in params {
            let sort = conv::conv_sort(self.genv, &param.sort, &mut || self.next_sort_var());
            self.insert_param(param.id, sort, param.kind);
        }
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
                for (t1, t2) in args1.iter().zip(args2.iter()) {
                    args.push(self.try_equate_inner(t1, t2)?);
                }
            }
            _ if sort1 == sort2 => {}
            _ => return None,
        }
        Some(sort1.clone())
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

    pub(crate) fn resolve_param_sort(&mut self, param: &fhir::RefineParam) -> Result {
        if let fhir::Sort::Infer = param.sort {
            let sort = self.param_sort(param.id);
            match self.fully_resolve(&sort) {
                Ok(sort) => {
                    self.wfckresults
                        .node_sorts_mut()
                        .insert(param.fhir_id, sort);
                }
                Err(_) => {
                    return Err(self.emit_err(errors::SortAnnotationNeeded::new(param)));
                }
            }
        }
        Ok(())
    }

    fn ensure_resolved_var(&mut self, path: &fhir::PathExpr) -> Result<rty::Sort> {
        let ExprRes::Param(_, id) = path.res else { span_bug!(path.span, "unexpected path") };
        let sort = self.param_sort(id);
        self.fully_resolve(&sort)
            .map_err(|_| self.emit_err(errors::CannotInferSort::new(path.span)))
    }

    fn is_single_field_record(&mut self, sort: &rty::Sort) -> Option<(DefId, rty::Sort)> {
        if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = sort
            && let [sort] = &sort_def.sorts(sort_args)[..]
        {
            Some((sort_def.did(), sort.clone()))
        } else {
            None
        }
    }

    pub(crate) fn into_results(self) -> WfckResults<'genv> {
        self.wfckresults
    }

    pub(crate) fn infer_mode(&self, id: fhir::ParamId) -> fhir::InferMode {
        let (sort, kind) = &self.params[&id];
        sort.infer_mode(*kind)
    }

    #[track_caller]
    pub(crate) fn param_sort(&self, id: fhir::ParamId) -> rty::Sort {
        self.params[&id].0.clone()
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
    pub(crate) fn infer(infcx: &'a mut InferCtxt<'genv, 'tcx>, node: &fhir::Node) -> Result {
        let errors = Errors::new(infcx.genv.sess());
        let mut vis = Self { infcx, errors };
        vis.visit_node(node);
        vis.errors.into_result()
    }

    fn infer_implicit_params(&mut self, idx: &fhir::RefineArg, expected: &rty::Sort) {
        match idx.kind {
            fhir::RefineArgKind::Expr(expr) => {
                if let fhir::ExprKind::Var(var, Some(_)) = &expr.kind {
                    let (_, id) = var.res.expect_param();
                    let found = self.infcx.param_sort(id);
                    self.infcx.equate(&found, expected);
                }
            }
            fhir::RefineArgKind::Abs(_, _) => {}
            fhir::RefineArgKind::Record(flds) => {
                if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = expected {
                    let sorts = sort_def.sorts(sort_args);
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
        }
    }
}

impl fhir::visit::Visitor for ImplicitParamInferer<'_, '_, '_> {
    fn visit_ty(&mut self, ty: &fhir::Ty) {
        if let fhir::TyKind::Indexed(bty, idx) = &ty.kind {
            if let Some(expected) = self.infcx.genv.sort_of_bty(bty) {
                self.infer_implicit_params(idx, &expected);
            } else if let Some(id) = idx.is_colon_param() {
                let found = self.infcx.param_sort(id);
                self.infcx.equate(&found, &rty::Sort::Err);
            } else {
                self.errors
                    .emit(errors::RefinedUnrefinableType::new(bty.span));
            }
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

    fn emit_field_not_found(
        &mut self,
        sort: &rty::Sort,
        field: fhir::SurfaceIdent,
    ) -> ErrorGuaranteed {
        self.emit_err(errors::FieldNotFound::new(sort.clone(), field))
    }

    #[track_caller]
    fn emit_err<'b>(&'b self, err: impl IntoDiagnostic<'b>) -> ErrorGuaranteed {
        self.genv.sess().emit_err(err)
    }
}

fn synth_lit(lit: fhir::Lit) -> rty::Sort {
    match lit {
        fhir::Lit::Int(_) => rty::Sort::Int,
        fhir::Lit::Bool(_) => rty::Sort::Bool,
        fhir::Lit::Real(_) => rty::Sort::Real,
    }
}

struct ShallowResolver<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
}

impl TypeFolder for ShallowResolver<'_, '_, '_> {
    fn fold_sort(&mut self, sort: &rty::Sort) -> rty::Sort {
        match sort {
            rty::Sort::Infer(rty::SortVar(vid)) => {
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
