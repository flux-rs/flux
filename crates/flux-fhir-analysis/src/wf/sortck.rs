use std::{collections::HashSet, iter};

use ena::unify::InPlaceUnificationTable;
use flux_common::{bug, iter::IterExt, span_bug};
use flux_errors::ErrorGuaranteed;
use flux_middle::{
    fhir::{self, FhirId, FluxOwnerId, WfckResults},
    global_env::GlobalEnv,
};
use itertools::izip;
use rustc_data_structures::unord::UnordMap;
use rustc_errors::IntoDiagnostic;
use rustc_span::Span;

use super::errors;

pub(super) struct InferCtxt<'a, 'tcx> {
    pub genv: &'a GlobalEnv<'a, 'tcx>,
    params: UnordMap<fhir::Name, (fhir::Sort, fhir::ParamKind)>,
    pub(super) unification_table: InPlaceUnificationTable<fhir::SortVid>,
    wfckresults: fhir::WfckResults,
    /// sort variables that can only be instantiated to sorts that support equality (i.e. non `FuncSort`)
    eq_vids: HashSet<fhir::SortVid>,
}

impl<'a, 'tcx> InferCtxt<'a, 'tcx> {
    pub(super) fn new(genv: &'a GlobalEnv<'a, 'tcx>, owner: FluxOwnerId) -> Self {
        Self {
            genv,
            wfckresults: fhir::WfckResults::new(owner),
            unification_table: InPlaceUnificationTable::new(),
            params: Default::default(),
            eq_vids: Default::default(),
        }
    }

    pub(super) fn check_refine_arg(
        &mut self,
        arg: &fhir::RefineArg,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match &arg.kind {
            fhir::RefineArgKind::Expr(expr) => self.check_expr(expr, expected),
            fhir::RefineArgKind::Abs(params, body) => {
                self.check_abs(params, body, arg.span, arg.fhir_id, expected)
            }
            fhir::RefineArgKind::Record(flds) => self.check_record(flds, arg.span, expected),
        }
    }

    fn check_abs(
        &mut self,
        params: &Vec<fhir::RefineParam>,
        body: &fhir::Expr,
        span: Span,
        fhir_id: FhirId,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        if let Some(fsort) = self.is_coercible_to_func(expected, fhir_id, fhir::Coercion::Inject) {
            let fsort = fsort.skip_binders();
            self.push_layer(params);

            if params.len() != fsort.inputs().len() {
                return Err(self.emit_err(errors::ParamCountMismatch::new(
                    span,
                    fsort.inputs().len(),
                    params.len(),
                )));
            }
            iter::zip(params, fsort.inputs()).try_for_each_exhaust(|(param, expected)| {
                let found = self.lookup_var(param.ident);
                if self.try_equate(&found, expected).is_none() {
                    return Err(self.emit_sort_mismatch(param.ident.span(), expected, &found));
                }
                Ok(())
            })?;
            self.check_expr(body, fsort.output())?;
            self.resolve_params_sorts(params)
        } else {
            Err(self.emit_err(errors::UnexpectedFun::new(span, expected)))
        }
    }

    fn check_record(
        &mut self,
        args: &[fhir::RefineArg],
        span: Span,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        if let fhir::Sort::Record(def_id, sort_args) = expected {
            let sorts = self.genv.index_sorts_of(*def_id, sort_args);
            if args.len() != sorts.len() {
                return Err(self.emit_err(errors::ArgCountMismatch::new(
                    Some(span),
                    String::from("type"),
                    sorts.len(),
                    args.len(),
                )));
            }
            izip!(args, sorts)
                .map(|(arg, expected)| self.check_refine_arg(arg, &expected))
                .try_collect_exhaust()
        } else {
            Err(self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("type"),
                1,
                args.len(),
            )))
        }
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
            | fhir::ExprKind::Var(..)
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
                if let Some(expected) =
                    self.is_coercible_to_numeric(expected, expr.fhir_id, fhir::Coercion::Inject)
                {
                    self.check_expr(e1, &expected)?;
                    self.check_expr(e2, &expected)?;
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
        if !self.is_coercible(&found, expected, expr.fhir_id) {
            return Err(self.emit_sort_mismatch(expr.span, expected, &found));
        }
        Ok(())
    }

    pub(super) fn check_loc(&mut self, loc: fhir::Ident) -> Result<(), ErrorGuaranteed> {
        let found = self.lookup_var(loc);
        if found == fhir::Sort::Loc {
            Ok(())
        } else {
            Err(self.emit_sort_mismatch(loc.span(), &fhir::Sort::Loc, &found))
        }
    }

    fn synth_expr(&mut self, expr: &fhir::Expr) -> Result<fhir::Sort, ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::Var(var, _) => Ok(self.lookup_var(*var)),
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
                let sort = self.ensure_resolved_var(*var)?;
                match &sort {
                    fhir::Sort::Record(def_id, sort_args) => {
                        self.genv
                            .field_sort(*def_id, sort_args.clone(), fld.name)
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
                let found = self.synth_expr(e1)?;
                if let Some(found) =
                    self.is_coercible_to_numeric(&found, e1.fhir_id, fhir::Coercion::Project)
                {
                    self.check_expr(e2, &found)?;
                    Ok(fhir::Sort::Bool)
                } else {
                    Err(self.emit_err(errors::ExpectedNumeric::new(e1.span, &found)))
                }
            }
            fhir::BinOp::Add | fhir::BinOp::Sub | fhir::BinOp::Mul | fhir::BinOp::Div => {
                let found = self.synth_expr(e1)?;
                if let Some(found) =
                    self.is_coercible_to_numeric(&found, e1.fhir_id, fhir::Coercion::Project)
                {
                    self.check_expr(e2, &found)?;
                    Ok(found)
                } else {
                    Err(self.emit_err(errors::ExpectedNumeric::new(e1.span, &found)))
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
        let func_sort = match func {
            fhir::Func::Var(var, fhir_id) => {
                let sort = self.lookup_var(*var);
                if let Some(fsort) =
                    self.is_coercible_to_func(&sort, *fhir_id, fhir::Coercion::Project)
                {
                    Ok(fsort)
                } else {
                    Err(self.emit_err(errors::ExpectedFun::new(var.span(), &sort)))
                }
            }
            fhir::Func::Global(func, _, span, _) => {
                Ok(self
                    .genv
                    .func_decl(func)
                    .unwrap_or_else(|| {
                        span_bug!(*span, "no definition found for uif `{func:?}` - {span:?}")
                    })
                    .sort
                    .clone())
            }
        };
        func_sort.map(|fsort| self.instantiate_func_sort(fsort))
    }

    fn instantiate_func_sort(&mut self, fsort: fhir::PolyFuncSort) -> fhir::FuncSort {
        let args: Vec<fhir::Sort> =
            std::iter::repeat_with(|| fhir::Sort::Infer(self.next_eq_sort_vid()))
                .take(fsort.params)
                .collect();
        fsort.instantiate(&args)
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
            self.params.insert(param.name(), (sort, param.kind));
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
        coercion: fhir::Coercion,
    ) -> Option<fhir::Sort> {
        if self.is_numeric(sort) {
            Some(sort.clone())
        } else if let Some(sort) = self.is_single_field_record(sort)
            && sort.is_numeric()
        {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![coercion]);
            Some(sort.clone())
        } else {
            None
        }
    }

    fn is_coercible_to_func(
        &mut self,
        sort: &fhir::Sort,
        fhir_id: FhirId,
        coercion: fhir::Coercion,
    ) -> Option<fhir::PolyFuncSort> {
        if let Some(fsort) = self.is_func(sort) {
            Some(fsort)
        } else if let Some(fhir::Sort::Func(fsort)) = self.is_single_field_record(sort) {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![coercion]);
            Some(fsort.clone())
        } else {
            None
        }
    }

    fn try_equate(&mut self, sort1: &fhir::Sort, sort2: &fhir::Sort) -> Option<fhir::Sort> {
        match (sort1, sort2) {
            (fhir::Sort::Infer(vid1), fhir::Sort::Infer(vid2)) => {
                self.unification_table.unify_var_var(*vid1, *vid2).ok()?;
                Some(fhir::Sort::Infer(*vid1))
            }
            (fhir::Sort::Infer(vid), sort) | (sort, fhir::Sort::Infer(vid))
                if !self.is_eq_sort_vid(*vid) || self.has_equality(sort) =>
            {
                self.unification_table
                    .unify_var_value(*vid, Some(sort.clone()))
                    .ok()?;
                Some(sort.clone())
            }
            (fhir::Sort::App(c1, args1), fhir::Sort::App(c2, args2)) => {
                if c1 != c2 || args1.len() != args2.len() {
                    return None;
                }
                let mut args = vec![];
                for (t1, t2) in args1.iter().zip(args2.iter()) {
                    args.push(self.try_equate(t1, t2)?);
                }
                Some(fhir::Sort::App(c1.clone(), args.into()))
            }
            _ if sort1 == sort2 => Some(sort1.clone()),
            _ => None,
        }
    }

    fn equate(&mut self, sort1: &fhir::Sort, sort2: &fhir::Sort) -> fhir::Sort {
        self.try_equate(sort1, sort2)
            .unwrap_or_else(|| bug!("failed to equate sorts: `{sort1:?}` `{sort2:?}`"))
    }

    fn next_sort_vid(&mut self) -> fhir::SortVid {
        self.unification_table.new_key(None)
    }

    fn next_eq_sort_vid(&mut self) -> fhir::SortVid {
        let vid = self.next_sort_vid();
        self.eq_vids.insert(vid);
        vid
    }

    fn is_eq_sort_vid(&self, vid: fhir::SortVid) -> bool {
        self.eq_vids.contains(&vid)
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
        if let fhir::Sort::Infer(vid) = self.params[&param.ident.name].0 {
            self.unification_table.probe_value(vid)
        } else {
            span_bug!(param.ident.span(), "expected wildcard sort")
        }
    }

    pub(crate) fn lookup_var(&mut self, var: fhir::Ident) -> fhir::Sort {
        let sort = self.params[&var.name].0.clone();
        self.resolve_sort(&sort).unwrap_or(sort)
    }

    fn ensure_resolved_var(&mut self, var: fhir::Ident) -> Result<fhir::Sort, ErrorGuaranteed> {
        let sort = self.params[&var.name].0.clone();
        if let Some(sort) = self.resolve_sort(&sort) {
            Ok(sort)
        } else {
            Err(self.emit_err(errors::CannotInferSort::new(var)))
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

    fn is_func(&mut self, sort: &fhir::Sort) -> Option<fhir::PolyFuncSort> {
        self.resolve_sort(sort).and_then(|s| {
            if let fhir::Sort::Func(fsort) = s {
                Some(fsort)
            } else {
                None
            }
        })
    }

    fn is_single_field_record(&mut self, sort: &fhir::Sort) -> Option<fhir::Sort> {
        self.resolve_sort(sort).and_then(|s| {
            if let fhir::Sort::Record(def_id, sort_args) = s
                && let [sort] = &self.genv.index_sorts_of(def_id, &sort_args)[..]
            {
                Some(sort.clone())
            } else {
                None
            }
        })
    }

    pub(crate) fn infer_implicit_params_ty(
        &mut self,
        ty: &fhir::Ty,
    ) -> Result<(), ErrorGuaranteed> {
        let mut vis = ImplicitParamInferer::new(self);
        fhir::visit::Visitor::visit_ty(&mut vis, ty);
        vis.into_result()
    }

    pub(crate) fn infer_implicit_params_constraint(
        &mut self,
        constr: &fhir::Constraint,
    ) -> Result<(), ErrorGuaranteed> {
        let mut vis = ImplicitParamInferer::new(self);
        fhir::visit::Visitor::visit_constraint(&mut vis, constr);
        vis.into_result()
    }

    fn has_equality(&mut self, sort: &fhir::Sort) -> bool {
        self.resolve_sort(sort)
            .map_or(false, |s| self.genv.has_equality(&s))
    }

    pub(crate) fn into_results(self) -> WfckResults {
        self.wfckresults
    }

    pub(crate) fn infer_mode(&self, var: fhir::Ident) -> fhir::InferMode {
        let (sort, kind) = &self.params[&var.name];
        kind.infer_mode(sort)
    }
}

struct ImplicitParamInferer<'a, 'b, 'tcx> {
    infcx: &'a mut InferCtxt<'b, 'tcx>,
    err: Option<ErrorGuaranteed>,
}

impl<'a, 'b, 'tcx> ImplicitParamInferer<'a, 'b, 'tcx> {
    fn new(infcx: &'a mut InferCtxt<'b, 'tcx>) -> Self {
        Self { infcx, err: None }
    }

    fn into_result(self) -> Result<(), ErrorGuaranteed> {
        if let Some(err) = self.err {
            Err(err)
        } else {
            Ok(())
        }
    }

    fn infer_implicit_params(
        &mut self,
        idx: &fhir::RefineArg,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match &idx.kind {
            fhir::RefineArgKind::Expr(expr) => {
                if let fhir::ExprKind::Var(var, Some(_)) = &expr.kind {
                    let found = self.infcx.lookup_var(*var);
                    self.infcx.equate(&found, expected);
                }
            }
            fhir::RefineArgKind::Abs(_, _) => {}
            fhir::RefineArgKind::Record(flds) => {
                if let fhir::Sort::Record(def_id, sort_args) = expected {
                    let sorts = self.infcx.genv.index_sorts_of(*def_id, sort_args);
                    if flds.len() != sorts.len() {
                        return Err(self.emit_err(errors::ArgCountMismatch::new(
                            Some(idx.span),
                            String::from("type"),
                            sorts.len(),
                            flds.len(),
                        )));
                    }
                    for (f, sort) in iter::zip(flds, sorts) {
                        self.infer_implicit_params(f, &sort)?;
                    }
                } else {
                    return Err(self.emit_err(errors::ArgCountMismatch::new(
                        Some(idx.span),
                        String::from("type"),
                        1,
                        flds.len(),
                    )));
                }
            }
        }
        Ok(())
    }

    #[track_caller]
    fn emit_err<'c>(&'c mut self, err: impl IntoDiagnostic<'c>) -> ErrorGuaranteed {
        let err = self.infcx.emit_err(err);
        self.err = Some(err);
        err
    }
}

impl fhir::visit::Visitor for ImplicitParamInferer<'_, '_, '_> {
    fn visit_ty(&mut self, ty: &fhir::Ty) {
        if let fhir::TyKind::Indexed(bty, idx) = &ty.kind {
            if let Some(expected) = self.infcx.genv.sort_of_bty(bty) {
                let _ = self.infer_implicit_params(idx, &expected);
            } else if let Some(var) = idx.is_colon_param() {
                let found = self.infcx.lookup_var(var);
                self.infcx.equate(&found, &fhir::Sort::Error);
            } else {
                let _ = self.emit_err(errors::RefinedUnrefinableType::new(bty.span));
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
        self.genv.sess.emit_err(err)
    }
}

fn synth_lit(lit: fhir::Lit) -> fhir::Sort {
    match lit {
        fhir::Lit::Int(_) => fhir::Sort::Int,
        fhir::Lit::Bool(_) => fhir::Sort::Bool,
        fhir::Lit::Real(_) => fhir::Sort::Real,
    }
}
