use std::{borrow::Borrow, iter};

use ena::unify::InPlaceUnificationTable;
use flux_common::{bug, iter::IterExt, span_bug};
use flux_errors::ErrorGuaranteed;
use flux_middle::{
    early_ctxt::EarlyCtxt,
    fhir::{self, FhirId, FluxOwnerId, WfckResults},
};
use itertools::izip;
use rustc_errors::IntoDiagnostic;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_span::Span;

use super::errors;

pub(super) struct InferCtxt<'a, 'tcx> {
    early_cx: &'a EarlyCtxt<'a, 'tcx>,
    sorts: FxHashMap<fhir::Name, fhir::Sort>,
    unification_table: InPlaceUnificationTable<fhir::SortVid>,
    wfckresults: fhir::WfckResults,
}

impl<'a, 'tcx> InferCtxt<'a, 'tcx> {
    pub(super) fn new(early_cx: &'a EarlyCtxt<'a, 'tcx>, owner: FluxOwnerId) -> Self {
        Self {
            early_cx,
            wfckresults: fhir::WfckResults::new(owner),
            unification_table: InPlaceUnificationTable::new(),
            sorts: FxHashMap::default(),
        }
    }

    pub(super) fn check_refine_arg(
        &mut self,
        arg: &fhir::RefineArg,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            fhir::RefineArg::Expr { expr, .. } => self.check_expr(expr, expected),
            fhir::RefineArg::Abs(params, body, span, fhir_id) => {
                self.check_abs(params, body, span, fhir_id, expected)
            }
            fhir::RefineArg::Record(def_id, flds, span) => {
                self.check_record(*def_id, flds, *span)?;
                let found = fhir::Sort::Record(*def_id);
                if &found != expected {
                    return Err(self.emit_sort_mismatch(*span, expected, &found));
                }
                Ok(())
            }
        }
    }

    fn check_abs(
        &mut self,
        params: &Vec<fhir::RefineParam>,
        body: &fhir::Expr,
        span: &Span,
        fhir_id: &FhirId,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        if let Some(fsort) = self.is_coercible_to_func(expected, *fhir_id) {
            self.push_layer(params);

            if params.len() != fsort.inputs().len() {
                return Err(self.emit_err(errors::ParamCountMismatch::new(
                    *span,
                    fsort.inputs().len(),
                    params.len(),
                )));
            }
            iter::zip(params, fsort.inputs()).try_for_each_exhaust(|(param, expected)| {
                let found = self[&param.ident.name].clone();
                if self.try_equate(&found, expected).is_none() {
                    return Err(self.emit_sort_mismatch(param.ident.span(), expected, &found));
                }
                Ok(())
            })?;
            self.check_expr(body, fsort.output())?;
            self.resolve_params_sorts(params)
        } else {
            Err(self.emit_err(errors::UnexpectedFun::new(*span, expected)))
        }
    }

    fn check_record(
        &mut self,
        def_id: DefId,
        args: &[fhir::RefineArg],
        span: Span,
    ) -> Result<(), ErrorGuaranteed> {
        let sorts = self.early_cx.index_sorts_of(def_id);
        if args.len() != sorts.len() {
            return Err(self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("type"),
                sorts.len(),
                args.len(),
            )));
        }
        izip!(args, sorts)
            .map(|(arg, expected)| self.check_refine_arg(arg, expected))
            .try_collect_exhaust()
    }

    pub(super) fn check_expr(
        &mut self,
        expr: &fhir::Expr,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => {
                self.check_binary_op(expr, *op, e1, e2, expected)?;
            }
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                self.check_expr(p, &fhir::Sort::Bool)?;
                self.check_expr(e1, expected)?;
                self.check_expr(e2, expected)?;
            }
            fhir::ExprKind::UnaryOp(_, _)
            | fhir::ExprKind::Dot(_, _)
            | fhir::ExprKind::App(_, _)
            | fhir::ExprKind::Const(_, _)
            | fhir::ExprKind::Var(_)
            | fhir::ExprKind::Literal(_) => {
                let found = self.synth_expr(expr)?;
                if !self.is_coercible(&found, expected, expr.fhir_id) {
                    return Err(self.emit_sort_mismatch(expr.span, expected, &found));
                }
            }
        }
        Ok(())
    }

    fn check_binary_op(
        &mut self,
        expr: &fhir::Expr,
        op: fhir::BinOp,
        e1: &fhir::Expr,
        e2: &fhir::Expr,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                if self.is_bool(expected) {
                    self.check_expr(e1, &fhir::Sort::Bool)?;
                    self.check_expr(e2, &fhir::Sort::Bool)?;
                    return Ok(());
                }
            }
            fhir::BinOp::Mod => {
                if self.is_int(expected) {
                    self.check_expr(e1, &fhir::Sort::Int)?;
                    self.check_expr(e2, &fhir::Sort::Int)?;
                    return Ok(());
                }
            }
            fhir::BinOp::Add | fhir::BinOp::Sub | fhir::BinOp::Mul | fhir::BinOp::Div => {
                if self.is_numeric(expected) {
                    self.check_expr(e1, expected)?;
                    self.check_expr(e2, expected)?;
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
        let found = self.synth_binary_op(expr, op, e1, e2)?;
        if &found != expected {
            return Err(self.emit_sort_mismatch(expr.span, expected, &found));
        }
        Ok(())
    }

    pub(super) fn check_loc(&mut self, loc: fhir::Ident) -> Result<(), ErrorGuaranteed> {
        let found = self[&loc.name].clone();
        if found == fhir::Sort::Loc {
            Ok(())
        } else {
            Err(self.emit_sort_mismatch(loc.span(), &fhir::Sort::Loc, &found))
        }
    }

    fn synth_expr(&mut self, expr: &fhir::Expr) -> Result<fhir::Sort, ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::Var(var) => Ok(self[var.name].clone()),
            fhir::ExprKind::Literal(lit) => Ok(synth_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => self.synth_binary_op(expr, *op, e1, e2),
            fhir::ExprKind::UnaryOp(op, e) => self.synth_unary_op(*op, e),
            fhir::ExprKind::Const(_, _) => Ok(fhir::Sort::Int), // TODO: generalize const sorts
            fhir::ExprKind::App(f, es) => self.synth_app(f, es, expr.span),
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                self.check_expr(p, &fhir::Sort::Bool)?;
                let sort = self.synth_expr(e1)?;
                self.check_expr(e2, &sort)?;
                Ok(sort)
            }
            fhir::ExprKind::Dot(var, fld) => {
                let sort = self[var.name].clone();
                match sort {
                    fhir::Sort::Record(def_id) => {
                        self.early_cx
                            .field_sort(def_id, fld.name)
                            .cloned()
                            .ok_or_else(|| self.emit_field_not_found(&sort, *fld))
                    }
                    fhir::Sort::Bool | fhir::Sort::Int | fhir::Sort::Real => {
                        Err(self.emit_err(errors::InvalidPrimitiveDotAccess::new(&sort, *fld)))
                    }
                    _ => Err(self.emit_field_not_found(&sort, *fld)),
                }
            }
        }
    }

    fn synth_binary_op(
        &mut self,
        expr: &fhir::Expr,
        op: fhir::BinOp,
        e1: &fhir::Expr,
        e2: &fhir::Expr,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                self.check_expr(e1, &fhir::Sort::Bool)?;
                self.check_expr(e2, &fhir::Sort::Bool)?;
                Ok(fhir::Sort::Bool)
            }
            fhir::BinOp::Eq | fhir::BinOp::Ne => {
                let s = self.synth_expr(e1)?;
                self.check_expr(e2, &s)?;
                if !self.has_equality(&s) {
                    return Err(self.emit_err(errors::NoEquality::new(expr.span, &s)));
                }
                Ok(fhir::Sort::Bool)
            }
            fhir::BinOp::Mod => {
                self.check_expr(e1, &fhir::Sort::Int)?;
                self.check_expr(e2, &fhir::Sort::Int)?;
                Ok(fhir::Sort::Int)
            }
            fhir::BinOp::Lt | fhir::BinOp::Le | fhir::BinOp::Gt | fhir::BinOp::Ge => {
                let sort = self.synth_expr(e1)?;
                if let Some(sort) = self.is_coercible_to_numeric(&sort, e1.fhir_id) {
                    self.check_expr(e2, &sort)?;
                    Ok(fhir::Sort::Bool)
                } else {
                    Err(self.emit_err(errors::ExpectedNumeric::new(e1.span, &sort)))
                }
            }
            fhir::BinOp::Add | fhir::BinOp::Sub | fhir::BinOp::Mul | fhir::BinOp::Div => {
                let sort = self.synth_expr(e1)?;
                if let Some(sort) = self.is_coercible_to_numeric(&sort, e1.fhir_id) {
                    self.check_expr(e2, &sort)?;
                    Ok(sort)
                } else {
                    Err(self.emit_err(errors::ExpectedNumeric::new(e1.span, &sort)))
                }
            }
        }
    }

    fn synth_unary_op(
        &mut self,
        op: fhir::UnOp,
        e: &fhir::Expr,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
        match op {
            fhir::UnOp::Not => {
                self.check_expr(e, &fhir::Sort::Bool)?;
                Ok(fhir::Sort::Bool)
            }
            fhir::UnOp::Neg => {
                self.check_expr(e, &fhir::Sort::Int)?;
                Ok(fhir::Sort::Int)
            }
        }
    }

    fn synth_app(
        &mut self,
        func: &fhir::Func,
        args: &[fhir::Expr],
        span: Span,
    ) -> Result<fhir::Sort, ErrorGuaranteed> {
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

    fn synth_func(&mut self, func: &fhir::Func) -> Result<fhir::FuncSort, ErrorGuaranteed> {
        match func {
            fhir::Func::Var(var, fhir_id) => {
                let sort = self[&var.name].clone();
                if let Some(fsort) = self.is_coercible_to_func(&sort, *fhir_id) {
                    Ok(fsort)
                } else {
                    Err(self.emit_err(errors::ExpectedFun::new(var.span(), &sort)))
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
}

impl<'a> InferCtxt<'a, '_> {
    /// Push a layer of binders. We assume all names are fresh so we don't care about shadowing
    pub(super) fn push_layer<'b>(
        &mut self,
        params: impl IntoIterator<Item = &'b fhir::RefineParam>,
    ) {
        for param in params {
            let sort = if param.sort == fhir::Sort::Wildcard {
                fhir::Sort::Infer(self.next_sort_vid())
            } else {
                param.sort.clone()
            };
            self.sorts.insert(param.name(), sort);
        }
    }

    /// Whether a value of `sort1` can be automatically coerced to a value of `sort2`. A value of a
    /// [`Record`] sort with a single field of sort `s` can be coerced to a value of sort `s` and vice
    /// versa, i.e., we can automatically project the field out of the record or inject a value into a
    /// record.
    ///
    /// [`Record`]: fhir::Sort::Record
    fn is_coercible(&mut self, sort1: &fhir::Sort, sort2: &fhir::Sort, fhir_id: FhirId) -> bool {
        if self.try_equate(sort1, sort2).is_some() {
            return true;
        }

        let mut sort1 = sort1.clone();
        let mut sort2 = sort2.clone();

        let mut coercions = vec![];
        if let Some(sort) = self.is_single_field_record(&sort1) {
            coercions.push(fhir::Coercion::Project);
            sort1 = sort.clone();
        }
        if let Some(sort) = self.is_single_field_record(&sort2) {
            coercions.push(fhir::Coercion::Inject);
            sort2 = sort.clone();
        }
        self.wfckresults.coercions_mut().insert(fhir_id, coercions);
        self.try_equate(&sort1, &sort2).is_some()
    }

    fn is_coercible_to_numeric(
        &mut self,
        sort: &fhir::Sort,
        fhir_id: FhirId,
    ) -> Option<fhir::Sort> {
        if self.is_numeric(sort) {
            Some(sort.clone())
        } else if let Some(sort) = self.is_single_field_record(sort) && sort.is_numeric() {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![fhir::Coercion::Project]);
            Some(sort.clone())
        } else {
            None
        }
    }

    fn is_coercible_to_func(
        &mut self,
        sort: &fhir::Sort,
        fhir_id: FhirId,
    ) -> Option<fhir::FuncSort> {
        if let Some(fsort) = self.is_func(sort) {
            Some(fsort)
        } else if let Some(fhir::Sort::Func(fsort)) = self.is_single_field_record(sort) {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![fhir::Coercion::Project]);
            Some(fsort.clone())
        } else {
            None
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

    pub(crate) fn resolve_params_sorts(
        &mut self,
        params: &[fhir::RefineParam],
    ) -> Result<(), ErrorGuaranteed> {
        params.iter().try_for_each_exhaust(|param| {
            if param.sort == fhir::Sort::Wildcard {
                if let Some(sort) = self.resolve_param(param) {
                    self.wfckresults
                        .node_sorts_mut()
                        .insert(param.fhir_id, sort);
                } else {
                    return Err(self.emit_err(errors::SortAnnotationNeeded::new(param)));
                }
            }
            Ok(())
        })
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

    fn is_single_field_record(&mut self, sort: &fhir::Sort) -> Option<&'a fhir::Sort> {
        self.resolve_sort(sort).and_then(|s| {
            if let fhir::Sort::Record(def_id) = s && let [sort] = self.early_cx.index_sorts_of(def_id) {
                Some(sort)
            } else {
                None
            }
        })
    }

    fn has_equality(&mut self, sort: &fhir::Sort) -> bool {
        self.resolve_sort(sort)
            .map_or(false, |s| self.early_cx.has_equality(&s))
    }

    pub(crate) fn into_results(self) -> WfckResults {
        self.wfckresults
    }
}

impl InferCtxt<'_, '_> {
    #[track_caller]
    fn emit_sort_mismatch(
        &mut self,
        span: Span,
        expected: &fhir::Sort,
        found: &fhir::Sort,
    ) -> ErrorGuaranteed {
        let expected = self
            .resolve_sort(expected)
            .unwrap_or_else(|| expected.clone());
        let found = self.resolve_sort(found).unwrap_or_else(|| found.clone());
        self.emit_err(errors::SortMismatch::new(span, expected, found))
    }

    fn emit_field_not_found(
        &mut self,
        sort: &fhir::Sort,
        field: fhir::SurfaceIdent,
    ) -> ErrorGuaranteed {
        let sort = self.resolve_sort(sort).unwrap_or_else(|| sort.clone());
        self.emit_err(errors::FieldNotFound::new(sort, field))
    }

    #[track_caller]
    fn emit_err<'b>(&'b self, err: impl IntoDiagnostic<'b>) -> ErrorGuaranteed {
        self.early_cx.emit_err(err)
    }
}

impl<T: Borrow<fhir::Name>> std::ops::Index<T> for InferCtxt<'_, '_> {
    type Output = fhir::Sort;

    fn index(&self, var: T) -> &Self::Output {
        self.sorts
            .get(var.borrow())
            .unwrap_or_else(|| bug!("no enty found for key: `{:?}`", var.borrow()))
    }
}

fn synth_lit(lit: fhir::Lit) -> fhir::Sort {
    match lit {
        fhir::Lit::Int(_) => fhir::Sort::Int,
        fhir::Lit::Bool(_) => fhir::Sort::Bool,
        fhir::Lit::Real(_) => fhir::Sort::Real,
    }
}
