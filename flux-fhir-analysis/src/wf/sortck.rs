use std::{borrow::Borrow, iter};

use flux_common::{bug, index::IndexGen, iter::IterExt, span_bug};
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
    sort_vid_gen: IndexGen<fhir::SortVid>,
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
        self.wfckresults
            .node_sorts_mut()
            .insert(arg.fhir_id(), expected.clone());

        match arg {
            fhir::RefineArg::Expr { expr, .. } => self.check_expr(env, expr, expected),
            fhir::RefineArg::Abs(params, body, span, fhir_id) => {
                if let Some(fsort) = self.is_coercible_to_func(expected, *fhir_id) {
                    if params.len() != fsort.inputs().len() {
                        return self.emit_err(errors::ParamCountMismatch::new(
                            *span,
                            fsort.inputs().len(),
                            params.len(),
                        ));
                    }
                    env.push_layer(
                        iter::zip(params, fsort.inputs()).map(|(param, sort)| {
                            fhir::RefineParam { sort: sort.clone(), ..*param }
                        }),
                    );
                    self.check_expr(env, body, fsort.output())
                } else {
                    self.emit_err(errors::UnexpectedFun::new(*span, expected))
                }
            }
            fhir::RefineArg::Aggregate(def_id, flds, span, _) => {
                self.check_aggregate(env, *def_id, flds, *span)?;
                let found = fhir::Sort::Aggregate(*def_id);
                if &found != expected {
                    return self.emit_err(errors::SortMismatch::new(*span, expected, &found));
                }
                Ok(())
            }
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
        env: &Env,
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
                if !self.is_coercible(&found, expected, expr.fhir_id) {
                    self.emit_err(errors::SortMismatch::new(expr.span, expected, &found))?;
                }
            }
        }
        Ok(())
    }

    fn check_binary_op(
        &mut self,
        env: &Env,
        expr: &fhir::Expr,
        op: fhir::BinOp,
        e1: &fhir::Expr,
        e2: &fhir::Expr,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                if matches!(expected, fhir::Sort::Bool) {
                    self.check_expr(env, e1, &fhir::Sort::Bool)?;
                    self.check_expr(env, e2, &fhir::Sort::Bool)?;
                    return Ok(());
                }
            }
            fhir::BinOp::Mod => {
                if matches!(expected, fhir::Sort::Int) {
                    self.check_expr(env, e1, &fhir::Sort::Int)?;
                    self.check_expr(env, e2, &fhir::Sort::Int)?;
                    return Ok(());
                }
            }
            fhir::BinOp::Add | fhir::BinOp::Sub | fhir::BinOp::Mul | fhir::BinOp::Div => {
                if expected.is_numeric() {
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
        if !self.is_coercible(&found, expected, expr.fhir_id) {
            self.emit_err(errors::SortMismatch::new(expr.span, expected, &found))?;
        }
        Ok(())
    }

    pub(super) fn check_loc(&self, env: &Env, loc: fhir::Ident) -> Result<(), ErrorGuaranteed> {
        let found = &env[&loc.name];
        if found == &fhir::Sort::Loc {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(loc.span(), &fhir::Sort::Loc, found))
        }
    }

    fn synth_expr(&mut self, env: &Env, expr: &fhir::Expr) -> Result<fhir::Sort, ErrorGuaranteed> {
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
                let sort = &env[var.name];
                match sort {
                    fhir::Sort::Aggregate(def_id) => {
                        self.early_cx
                            .field_sort(*def_id, fld.name)
                            .cloned()
                            .ok_or_else(|| {
                                self.early_cx
                                    .emit_err(errors::FieldNotFound::new(sort, *fld))
                            })
                    }
                    fhir::Sort::Bool | fhir::Sort::Int | fhir::Sort::Real => {
                        self.emit_err(errors::InvalidPrimitiveDotAccess::new(sort, *fld))
                    }
                    _ => self.emit_err(errors::FieldNotFound::new(sort, *fld)),
                }
            }
        }
    }

    fn synth_binary_op(
        &mut self,
        env: &Env,
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
                if !self.early_cx.has_equality(&s) {
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
                if let Some(sort) = self.is_coercible_to_numeric(&sort, e1.fhir_id) {
                    self.check_expr(env, e2, &sort)?;
                    Ok(fhir::Sort::Bool)
                } else {
                    self.emit_err(errors::ExpectedNumeric::new(e1.span, &sort))
                }
            }
            fhir::BinOp::Add | fhir::BinOp::Sub | fhir::BinOp::Mul | fhir::BinOp::Div => {
                let sort = self.synth_expr(env, e1)?;
                if let Some(sort) = self.is_coercible_to_numeric(&sort, e1.fhir_id) {
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
        env: &Env,
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
        env: &Env,
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
        env: &Env,
        func: &fhir::Func,
    ) -> Result<fhir::FuncSort, ErrorGuaranteed> {
        match func {
            fhir::Func::Var(var, fhir_id) => {
                let sort = &env[&var.name];
                if let Some(fsort) = self.is_coercible_to_func(sort, *fhir_id) {
                    Ok(fsort)
                } else {
                    self.emit_err(errors::ExpectedFun::new(var.span(), sort))
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
    fn is_coercible(&mut self, sort1: &fhir::Sort, sort2: &fhir::Sort, fhir_id: FhirId) -> bool {
        if sort1 == sort2 {
            return true;
        }
        let mut sort1 = sort1.clone();
        let mut sort2 = sort2.clone();
        let mut coercions = vec![];
        if let Some(sort) = self.is_single_field_aggregate(&sort1) {
            coercions.push(fhir::Coercion::Project);
            sort1 = sort.clone();
        }
        if let Some(sort) = self.is_single_field_aggregate(&sort2) {
            coercions.push(fhir::Coercion::Inject);
            sort2 = sort.clone();
        }
        self.wfckresults.coercions_mut().insert(fhir_id, coercions);
        sort1 == sort2
    }

    fn is_coercible_to_func(
        &mut self,
        sort: &fhir::Sort,
        fhir_id: FhirId,
    ) -> Option<fhir::FuncSort> {
        if let fhir::Sort::Func(fsort) = sort {
            Some(fsort.clone())
        } else if let Some(fhir::Sort::Func(fsort)) = self.is_single_field_aggregate(sort) {
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
        sort: &fhir::Sort,
        fhir_id: FhirId,
    ) -> Option<fhir::Sort> {
        if sort.is_numeric() {
            Some(sort.clone())
        } else if let Some(sort) = self.is_single_field_aggregate(sort) && sort.is_numeric() {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![fhir::Coercion::Project]);
            Some(sort.clone())
        } else {
            None
        }
    }

    fn is_single_field_aggregate(&self, sort: &fhir::Sort) -> Option<&'a fhir::Sort> {
        self.early_cx.is_single_field_aggregate(sort)
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

    fn next_sort_vid(&self) -> fhir::SortVid {
        self.sort_vid_gen.fresh()
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
        let sort_vid_gen = IndexGen::new();
        Env {
            sorts: iter
                .into_iter()
                .map(|param| {
                    let sort = if param.sort == fhir::Sort::Wildcard {
                        fhir::Sort::Infer(sort_vid_gen.fresh())
                    } else {
                        param.sort.clone()
                    };
                    (param.name(), sort)
                })
                .collect(),
            sort_vid_gen,
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
