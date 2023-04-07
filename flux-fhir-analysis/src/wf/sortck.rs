use std::{borrow::Borrow, iter};

use ena::unify::InPlaceUnificationTable;
use flux_common::{bug, iter::IterExt, span_bug};
use flux_errors::ErrorGuaranteed;
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir::{self, FhirId},
};
use itertools::izip;
use rustc_errors::IntoDiagnostic;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_span::Span;

use super::errors;

pub(super) struct SortChecker<'a, 'tcx> {
    early_cx: &'a EarlyCtxt<'a, 'tcx>,
    wfckresults: &'a mut fhir::WfckResults,
}

#[derive(Default)]
pub(super) struct Env {
    sorts: FxHashMap<fhir::Name, fhir::Sort>,
    unification_table: InPlaceUnificationTable<fhir::SortVid>,
}

impl<'a, 'tcx> SortChecker<'a, 'tcx> {
    pub(super) fn new(
        early_cx: &'a EarlyCtxt<'a, 'tcx>,
        wfckresults: &'a mut fhir::WfckResults,
    ) -> Self {
        Self { early_cx, wfckresults }
    }

    pub(super) fn check_refine_arg(
        &mut self,
        env: &mut Env,
        arg: &fhir::RefineArg,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            fhir::RefineArg::Expr { expr, .. } => self.check_expr(env, expr, expected),
            fhir::RefineArg::Abs(params, body, span, fhir_id) => {
                self.check_abs(env, params, body, span, fhir_id, expected)
            }
            fhir::RefineArg::Aggregate(def_id, flds, span, _) => {
                self.check_aggregate(env, *def_id, flds, *span)?;
                let found = fhir::Sort::Aggregate(*def_id);
                if &found != expected {
                    return self.emit_err(env.sort_mismatch(*span, expected, &found));
                }
                Ok(())
            }
        }
    }

    fn check_abs(
        &mut self,
        env: &mut Env,
        params: &Vec<fhir::RefineParam>,
        body: &fhir::Expr,
        span: &Span,
        fhir_id: &FhirId,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        if let Some(fsort) = self.is_coercible_to_func(env, expected, *fhir_id) {
            env.push_layer(params.iter().cloned());

            if params.len() != fsort.inputs().len() {
                return self.emit_err(errors::ParamCountMismatch::new(
                    *span,
                    fsort.inputs().len(),
                    params.len(),
                ));
            }
            iter::zip(params, fsort.inputs()).try_for_each_exhaust(|(param, expected)| {
                let found = env[&param.ident.name].clone();
                if env.try_equate(&found, expected).is_none() {
                    return self.emit_err(env.sort_mismatch(param.ident.span(), expected, &found));
                }
                Ok(())
            })?;
            self.check_expr(env, body, fsort.output())?;
            self.resolve_params_sorts(env, params)
        } else {
            self.emit_err(errors::UnexpectedFun::new(*span, expected))
        }
    }

    fn check_aggregate(
        &mut self,
        env: &mut Env,
        def_id: DefId,
        args: &[fhir::RefineArg],
        span: Span,
    ) -> Result<(), ErrorGuaranteed> {
        let sorts = self.early_cx.index_sorts_of(def_id);
        if args.len() != sorts.len() {
            return self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("type"),
                sorts.len(),
                args.len(),
            ));
        }
        izip!(args, sorts)
            .map(|(arg, expected)| self.check_refine_arg(env, arg, expected))
            .try_collect_exhaust()
    }

    pub(super) fn check_expr(
        &mut self,
        env: &mut Env,
        expr: &fhir::Expr,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => {
                self.check_binary_op(env, expr, *op, e1, e2, expected)?;
            }
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                self.check_expr(env, p, &fhir::Sort::Bool)?;
                self.check_expr(env, e1, expected)?;
                self.check_expr(env, e2, expected)?;
            }
            fhir::ExprKind::UnaryOp(_, _)
            | fhir::ExprKind::Dot(_, _)
            | fhir::ExprKind::App(_, _)
            | fhir::ExprKind::Const(_, _)
            | fhir::ExprKind::Var(_)
            | fhir::ExprKind::Literal(_) => {
                let found = self.synth_expr(env, expr)?;
                if !self.is_coercible(env, &found, expected, expr.fhir_id) {
                    self.emit_err(env.sort_mismatch(expr.span, expected, &found))?;
                }
            }
        }
        Ok(())
    }

    fn check_binary_op(
        &mut self,
        env: &mut Env,
        expr: &fhir::Expr,
        op: fhir::BinOp,
        e1: &fhir::Expr,
        e2: &fhir::Expr,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                if env.is_bool(expected) {
                    self.check_expr(env, e1, &fhir::Sort::Bool)?;
                    self.check_expr(env, e2, &fhir::Sort::Bool)?;
                    return Ok(());
                }
            }
            fhir::BinOp::Mod => {
                if env.is_int(expected) {
                    self.check_expr(env, e1, &fhir::Sort::Int)?;
                    self.check_expr(env, e2, &fhir::Sort::Int)?;
                    return Ok(());
                }
            }
            fhir::BinOp::Add | fhir::BinOp::Sub | fhir::BinOp::Mul | fhir::BinOp::Div => {
                if env.is_numeric(expected) {
                    self.check_expr(env, e1, expected)?;
                    self.check_expr(env, e2, expected)?;
                    return Ok(());
                }
            }
            fhir::BinOp::Eq
            | fhir::BinOp::Ne
            | fhir::BinOp::Lt
            | fhir::BinOp::Le
            | fhir::BinOp::Gt
            | fhir::BinOp::Ge => {}
        }
        let found = self.synth_binary_op(env, expr, op, e1, e2)?;
        if &found != expected {
            self.emit_err(env.sort_mismatch(expr.span, expected, &found))?;
        }
        Ok(())
    }

    pub(super) fn check_loc(&self, env: &mut Env, loc: fhir::Ident) -> Result<(), ErrorGuaranteed> {
        let found = env[&loc.name].clone();
        if found == fhir::Sort::Loc {
            Ok(())
        } else {
            self.emit_err(env.sort_mismatch(loc.span(), &fhir::Sort::Loc, &found))
        }
    }

    fn synth_expr(
        &mut self,
        env: &mut Env,
        expr: &fhir::Expr,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::Var(var) => Ok(env[var.name].clone()),
            fhir::ExprKind::Literal(lit) => Ok(synth_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => {
                self.synth_binary_op(env, expr, *op, e1, e2)
            }
            fhir::ExprKind::UnaryOp(op, e) => self.synth_unary_op(env, *op, e),
            fhir::ExprKind::Const(_, _) => Ok(fhir::Sort::Int), // TODO: generalize const sorts
            fhir::ExprKind::App(f, es) => self.synth_app(env, f, es, expr.span),
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                self.check_expr(env, p, &fhir::Sort::Bool)?;
                let sort = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, &sort)?;
                Ok(sort)
            }
            fhir::ExprKind::Dot(var, fld) => {
                let sort = env[var.name].clone();
                match sort {
                    fhir::Sort::Aggregate(def_id) => {
                        self.early_cx
                            .field_sort(def_id, fld.name)
                            .cloned()
                            .ok_or_else(|| self.early_cx.emit_err(env.field_not_found(&sort, *fld)))
                    }
                    fhir::Sort::Bool | fhir::Sort::Int | fhir::Sort::Real => {
                        self.emit_err(errors::InvalidPrimitiveDotAccess::new(&sort, *fld))
                    }
                    _ => self.emit_err(env.field_not_found(&sort, *fld)),
                }
            }
        }
    }

    fn synth_binary_op(
        &mut self,
        env: &mut Env,
        expr: &fhir::Expr,
        op: fhir::BinOp,
        e1: &fhir::Expr,
        e2: &fhir::Expr,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                self.check_expr(env, e1, &fhir::Sort::Bool)?;
                self.check_expr(env, e2, &fhir::Sort::Bool)?;
                Ok(fhir::Sort::Bool)
            }
            fhir::BinOp::Eq | fhir::BinOp::Ne => {
                let s = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, &s)?;
                if !self.has_equality(env, &s) {
                    return self.emit_err(errors::NoEquality::new(expr.span, &s));
                }
                Ok(fhir::Sort::Bool)
            }
            fhir::BinOp::Mod => {
                self.check_expr(env, e1, &fhir::Sort::Int)?;
                self.check_expr(env, e2, &fhir::Sort::Int)?;
                Ok(fhir::Sort::Int)
            }
            fhir::BinOp::Lt | fhir::BinOp::Le | fhir::BinOp::Gt | fhir::BinOp::Ge => {
                let sort = self.synth_expr(env, e1)?;
                if let Some(sort) = self.is_coercible_to_numeric(env, &sort, e1.fhir_id) {
                    self.check_expr(env, e2, &sort)?;
                    Ok(fhir::Sort::Bool)
                } else {
                    self.emit_err(errors::ExpectedNumeric::new(e1.span, &sort))
                }
            }
            fhir::BinOp::Add | fhir::BinOp::Sub | fhir::BinOp::Mul | fhir::BinOp::Div => {
                let sort = self.synth_expr(env, e1)?;
                if let Some(sort) = self.is_coercible_to_numeric(env, &sort, e1.fhir_id) {
                    self.check_expr(env, e2, &sort)?;
                    Ok(sort)
                } else {
                    self.emit_err(errors::ExpectedNumeric::new(e1.span, &sort))
                }
            }
        }
    }

    fn synth_unary_op(
        &mut self,
        env: &mut Env,
        op: fhir::UnOp,
        e: &fhir::Expr,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
        match op {
            fhir::UnOp::Not => {
                self.check_expr(env, e, &fhir::Sort::Bool)?;
                Ok(fhir::Sort::Bool)
            }
            fhir::UnOp::Neg => {
                self.check_expr(env, e, &fhir::Sort::Int)?;
                Ok(fhir::Sort::Int)
            }
        }
    }

    fn synth_app(
        &mut self,
        env: &mut Env,
        func: &fhir::Func,
        args: &[fhir::Expr],
        span: Span,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
        let fsort = self.synth_func(env, func)?;
        if args.len() != fsort.inputs().len() {
            return self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("function"),
                fsort.inputs().len(),
                args.len(),
            ));
        }

        iter::zip(args, fsort.inputs())
            .try_for_each_exhaust(|(arg, formal)| self.check_expr(env, arg, formal))?;

        Ok(fsort.output().clone())
    }

    fn synth_func(
        &mut self,
        env: &mut Env,
        func: &fhir::Func,
    ) -> Result<fhir::FuncSort, ErrorGuaranteed> {
        match func {
            fhir::Func::Var(var, fhir_id) => {
                let sort = env[&var.name].clone();
                if let Some(fsort) = self.is_coercible_to_func(env, &sort, *fhir_id) {
                    Ok(fsort)
                } else {
                    self.emit_err(errors::ExpectedFun::new(var.span(), &sort))
                }
            }
            fhir::Func::Global(func, _, span, _) => {
                Ok(self
                    .early_cx
                    .func_decl(func)
                    .unwrap_or_else(|| {
                        span_bug!(*span, "no definition found for uif `{func:?}` - {span:?}")
                    })
                    .sort
                    .clone())
            }
        }
    }

    /// Whether a value of `sort1` can be automatically coerced to a value of `sort2`. A value of an
    /// [`Aggregate`] sort with a single field of sort `s` can be coerced to a value of sort `s` and vice
    /// versa, i.e., we can automatically project the field out of the adt or inject a value into an
    /// adt.
    ///
    /// [`Aggregate`]: fhir::Sort::Aggregate
    fn is_coercible(
        &mut self,
        env: &mut Env,
        sort1: &fhir::Sort,
        sort2: &fhir::Sort,
        fhir_id: FhirId,
    ) -> bool {
        if env.try_equate(sort1, sort2).is_some() {
            return true;
        }
        let mut sort1 = sort1.clone();
        let mut sort2 = sort2.clone();
        let mut coercions = vec![];
        if let Some(sort) = self.is_single_field_aggregate(env, &sort1) {
            coercions.push(fhir::Coercion::Project);
            sort1 = sort.clone();
        }
        if let Some(sort) = self.is_single_field_aggregate(env, &sort2) {
            coercions.push(fhir::Coercion::Inject);
            sort2 = sort.clone();
        }
        self.wfckresults.coercions_mut().insert(fhir_id, coercions);
        env.try_equate(&sort1, &sort2).is_some()
    }

    fn is_coercible_to_func(
        &mut self,
        env: &mut Env,
        sort: &fhir::Sort,
        fhir_id: FhirId,
    ) -> Option<fhir::FuncSort> {
        if let Some(fsort) = env.is_func(sort) {
            Some(fsort)
        } else if let Some(fhir::Sort::Func(fsort)) = self.is_single_field_aggregate(env, sort) {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![fhir::Coercion::Project]);
            Some(fsort.clone())
        } else {
            None
        }
    }

    fn is_coercible_to_numeric(
        &mut self,
        env: &mut Env,
        sort: &fhir::Sort,
        fhir_id: FhirId,
    ) -> Option<fhir::Sort> {
        if env.is_numeric(sort) {
            Some(sort.clone())
        } else if let Some(sort) = self.is_single_field_aggregate(env, sort) && sort.is_numeric() {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![fhir::Coercion::Project]);
            Some(sort.clone())
        } else {
            None
        }
    }

    fn is_single_field_aggregate(
        &self,
        env: &mut Env,
        sort: &fhir::Sort,
    ) -> Option<&'a fhir::Sort> {
        env.is_single_field_aggregate(self.early_cx, sort)
    }

    fn has_equality(&self, env: &mut Env, sort: &fhir::Sort) -> bool {
        env.has_equality(self.early_cx, sort)
    }

    pub(crate) fn resolve_params_sorts(
        &mut self,
        env: &mut Env,
        params: &[fhir::RefineParam],
    ) -> Result<(), ErrorGuaranteed> {
        params.iter().try_for_each_exhaust(|param| {
            if param.sort == fhir::Sort::Wildcard {
                if let Some(sort) = env.resolve_param(param) {
                    self.wfckresults
                        .node_sorts_mut()
                        .insert(param.fhir_id, sort);
                } else {
                    return self.emit_err(errors::SortAnnotationNeeded::new(param));
                }
            }
            Ok(())
        })
    }

    #[track_caller]
    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R, ErrorGuaranteed> {
        Err(self.early_cx.emit_err(err))
    }
}

impl Env {
    /// Push a layer of binders. We assume all names are fresh so we don't care about shadowing
    pub(super) fn push_layer(&mut self, params: impl IntoIterator<Item = fhir::RefineParam>) {
        for param in params {
            let sort = if param.sort == fhir::Sort::Wildcard {
                fhir::Sort::Infer(self.next_sort_vid())
            } else {
                param.sort.clone()
            };
            self.sorts.insert(param.name(), sort);
        }
    }

    fn try_equate(&mut self, sort1: &fhir::Sort, sort2: &fhir::Sort) -> Option<fhir::Sort> {
        match (sort1, sort2) {
            (fhir::Sort::Infer(vid1), fhir::Sort::Infer(vid2)) => {
                self.unification_table.unify_var_var(*vid2, *vid2).ok()?;
                Some(fhir::Sort::Infer(*vid1))
            }
            (fhir::Sort::Infer(vid), sort) | (sort, fhir::Sort::Infer(vid)) => {
                self.unification_table
                    .unify_var_value(*vid, Some(sort.clone()))
                    .ok()?;
                Some(sort.clone())
            }
            _ if sort1 == sort2 => Some(sort1.clone()),
            _ => None,
        }
    }

    fn next_sort_vid(&mut self) -> fhir::SortVid {
        self.unification_table.new_key(None)
    }

    fn resolve_param(&mut self, param: &fhir::RefineParam) -> Option<fhir::Sort> {
        if let fhir::Sort::Infer(vid) = self.sorts[&param.ident.name] {
            self.unification_table.probe_value(vid)
        } else {
            span_bug!(param.ident.span(), "expected wildcard sort")
        }
    }

    fn resolve_sort(&mut self, sort: &fhir::Sort) -> Option<fhir::Sort> {
        if let fhir::Sort::Infer(vid) = sort {
            self.unification_table.probe_value(*vid)
        } else {
            Some(sort.clone())
        }
    }

    fn is_numeric(&mut self, sort: &fhir::Sort) -> bool {
        self.resolve_sort(sort).map_or(false, |s| s.is_numeric())
    }

    fn is_bool(&mut self, sort: &fhir::Sort) -> bool {
        self.resolve_sort(sort).map_or(false, |s| s.is_bool())
    }

    fn is_int(&mut self, sort: &fhir::Sort) -> bool {
        self.resolve_sort(sort)
            .map_or(false, |s| matches!(s, fhir::Sort::Int))
    }

    fn is_func(&mut self, sort: &fhir::Sort) -> Option<fhir::FuncSort> {
        self.resolve_sort(sort).and_then(|s| {
            if let fhir::Sort::Func(fsort) = s {
                Some(fsort)
            } else {
                None
            }
        })
    }

    fn is_single_field_aggregate<'a>(
        &mut self,
        early_cx: &'a EarlyCtxt,
        sort: &fhir::Sort,
    ) -> Option<&'a fhir::Sort> {
        self.resolve_sort(sort)
            .and_then(|s| early_cx.is_single_field_aggregate(&s))
    }

    fn has_equality(&mut self, early_cx: &EarlyCtxt, sort: &fhir::Sort) -> bool {
        self.resolve_sort(sort)
            .map_or(false, |s| early_cx.has_equality(&s))
    }

    fn sort_mismatch(
        &mut self,
        span: Span,
        expected: &fhir::Sort,
        found: &fhir::Sort,
    ) -> errors::SortMismatch {
        let expected = self
            .resolve_sort(expected)
            .unwrap_or_else(|| expected.clone());
        let found = self.resolve_sort(found).unwrap_or_else(|| found.clone());
        errors::SortMismatch::new(span, expected, found)
    }

    fn field_not_found(
        &mut self,
        sort: &fhir::Sort,
        field: fhir::SurfaceIdent,
    ) -> errors::FieldNotFound {
        let sort = self.resolve_sort(sort).unwrap_or_else(|| sort.clone());
        errors::FieldNotFound::new(sort, field)
    }
}

impl<T: Borrow<fhir::Name>> std::ops::Index<T> for Env {
    type Output = fhir::Sort;

    fn index(&self, var: T) -> &Self::Output {
        self.sorts
            .get(var.borrow())
            .unwrap_or_else(|| bug!("no enty found for key: `{:?}`", var.borrow()))
    }
}

impl From<&[fhir::RefineParam]> for Env {
    fn from(params: &[fhir::RefineParam]) -> Self {
        Env::from_iter(params.iter())
    }
}

impl<'a> FromIterator<&'a fhir::RefineParam> for Env {
    fn from_iter<T: IntoIterator<Item = &'a fhir::RefineParam>>(iter: T) -> Self {
        let mut unification_table = InPlaceUnificationTable::default();
        Env {
            sorts: iter
                .into_iter()
                .map(|param| {
                    let sort = if param.sort == fhir::Sort::Wildcard {
                        fhir::Sort::Infer(unification_table.new_key(None))
                    } else {
                        param.sort.clone()
                    };
                    (param.name(), sort)
                })
                .collect(),
            unification_table,
        }
    }
}

fn synth_lit(lit: fhir::Lit) -> fhir::Sort {
    match lit {
        fhir::Lit::Int(_) => fhir::Sort::Int,
        fhir::Lit::Bool(_) => fhir::Sort::Bool,
        fhir::Lit::Real(_) => fhir::Sort::Real,
    }
}
