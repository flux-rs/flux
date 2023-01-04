//! Checks type well-formedness
//!
//! Well-formedness checking assumes names are correctly bound which is guaranteed after desugaring.
use std::{borrow::Borrow, iter};

use flux_common::iter::IterExt;
use flux_errors::FluxSession;
use flux_middle::fhir;
use itertools::izip;
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

pub struct Wf<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    sess: &'a FluxSession,
    map: &'a fhir::Map,
    modes: FxHashMap<fhir::Name, fhir::InferMode>,
}

struct Env {
    sorts: FxHashMap<fhir::Name, fhir::Sort>,
}

impl Env {
    fn with_binders<R>(
        &mut self,
        binders: &[fhir::Name],
        sorts: &[fhir::Sort],
        f: impl FnOnce(&Self) -> R,
    ) -> R {
        debug_assert_eq!(binders.len(), sorts.len());
        for (binder, sort) in iter::zip(binders, sorts) {
            self.sorts.insert(*binder, sort.clone());
        }
        let r = f(self);
        for binder in binders {
            self.sorts.remove(binder);
        }
        r
    }
}

impl From<&[fhir::RefineParam]> for Env {
    fn from(params: &[fhir::RefineParam]) -> Env {
        let sorts = params
            .iter()
            .map(|param| (param.name.name, param.sort.clone()))
            .collect();
        Env { sorts }
    }
}

impl From<&[(fhir::Ident, fhir::Sort)]> for Env {
    fn from(params: &[(fhir::Ident, fhir::Sort)]) -> Self {
        Env {
            sorts: params
                .iter()
                .map(|(ident, sort)| (ident.name, sort.clone()))
                .collect(),
        }
    }
}

impl<T: Borrow<fhir::Name>> std::ops::Index<T> for Env {
    type Output = fhir::Sort;

    fn index(&self, var: T) -> &Self::Output {
        self.sorts
            .get(var.borrow())
            .unwrap_or_else(|| panic!("no enty found for key: `{:?}`", var.borrow()))
    }
}

impl Wf<'_, '_> {
    pub fn check_qualifier(
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        qualifier: &fhir::Qualifier,
    ) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(tcx, sess, map);
        let env = Env::from(&qualifier.args[..]);

        wf.check_expr(&env, &qualifier.expr, &fhir::Sort::Bool)
    }

    pub fn check_defn(
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        defn: &fhir::Defn,
    ) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(tcx, sess, map);
        let env = Env::from(&defn.args[..]);
        wf.check_expr(&env, &defn.expr, &defn.sort)
    }

    pub fn check_adt_def(
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        adt_def: &fhir::AdtDef,
    ) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(tcx, sess, map);
        let env = Env::from(&adt_def.refined_by.params[..]);
        adt_def
            .invariants
            .iter()
            .try_for_each_exhaust(|invariant| wf.check_expr(&env, invariant, &fhir::Sort::Bool))?;

        Ok(())
    }

    pub fn check_fn_sig(
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        fn_sig: &fhir::FnSig,
    ) -> Result<(), ErrorGuaranteed> {
        let mut wf = Wf::new(tcx, sess, map);
        for param in &fn_sig.params {
            wf.modes.insert(param.name.name, param.mode);
        }
        let mut env = Env::from(&fn_sig.params[..]);

        let args = fn_sig
            .args
            .iter()
            .try_for_each_exhaust(|ty| wf.check_type(&mut env, ty));

        let requires = fn_sig
            .requires
            .iter()
            .try_for_each_exhaust(|constr| wf.check_constr(&mut env, constr));

        let ensures = fn_sig
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| wf.check_constr(&mut env, constr));

        let ret = wf.check_type(&mut env, &fn_sig.ret);

        let constrs = wf.check_constrs(fn_sig);

        args?;
        ret?;
        ensures?;
        requires?;
        constrs?;

        Ok(())
    }

    pub fn check_struct_def(
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        refined_by: &fhir::RefinedBy,
        def: &fhir::StructDef,
    ) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(tcx, sess, map);
        let mut env = Env::from(&refined_by.params[..]);
        if let fhir::StructKind::Transparent { fields } = &def.kind {
            fields.iter().try_for_each_exhaust(|ty| {
                if let Some(ty) = ty {
                    wf.check_type(&mut env, ty)
                } else {
                    Ok(())
                }
            })?;
        }
        Ok(())
    }

    pub fn check_enum_def(
        tcx: TyCtxt,
        sess: &FluxSession,
        map: &fhir::Map,
        def: &fhir::EnumDef,
    ) -> Result<(), ErrorGuaranteed> {
        let wf = Wf::new(tcx, sess, map);
        def.variants
            .iter()
            .try_for_each_exhaust(|variant| wf.check_variant(variant))
    }
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, sess: &'a FluxSession, map: &'a fhir::Map) -> Self {
        Wf { tcx, sess, map, modes: FxHashMap::default() }
    }

    fn check_variant(&self, variant: &fhir::VariantDef) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::from(&variant.params[..]);
        let fields = variant
            .fields
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty));
        let indices = self.check_index(&mut env, &variant.ret.idx, &variant.ret.bty.sort());
        fields?;
        indices?;
        Ok(())
    }

    fn check_constrs(&self, fn_sig: &fhir::FnSig) -> Result<(), ErrorGuaranteed> {
        let mut output_locs = FxHashSet::default();
        fn_sig.ensures.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, _) = constr
               && !output_locs.insert(loc.name)
            {
                self.emit_err(errors::DuplicatedEnsures::new(loc))
            } else {
                Ok(())
            }
        })?;

        fn_sig.requires.iter().try_for_each_exhaust(|constr| {
            if let fhir::Constraint::Type(loc, _) = constr
               && !output_locs.contains(&loc.name)
            {
                self.emit_err(errors::MissingEnsures::new(loc))
            } else {
                Ok(())
            }
        })
    }

    fn check_constr(
        &self,
        env: &mut Env,
        constr: &fhir::Constraint,
    ) -> Result<(), ErrorGuaranteed> {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                [self.check_loc(env, *loc), self.check_type(env, ty)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            fhir::Constraint::Pred(pred) => self.check_pred(env, pred),
        }
    }

    fn check_type(&self, env: &mut Env, ty: &fhir::Ty) -> Result<(), ErrorGuaranteed> {
        match ty {
            fhir::Ty::BaseTy(bty) => self.check_base_ty(env, bty),
            fhir::Ty::Indexed(bty, refine) => {
                self.check_index(env, refine, &bty.sort())?;
                self.check_base_ty(env, bty)
            }
            fhir::Ty::Exists(bty, bind, pred) => {
                let sort = bty.sort();
                self.check_base_ty(env, bty)?;
                env.with_binders(&[bind.name], &[sort], |env| self.check_pred(env, pred))
            }
            fhir::Ty::Ptr(loc) => self.check_loc(env, *loc),
            fhir::Ty::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(env, ty))
            }
            fhir::Ty::Array(ty, _) => self.check_type(env, ty),
            fhir::Ty::Constr(pred, ty) => {
                self.check_pred(env, pred)?;
                self.check_type(env, ty)
            }
            fhir::Ty::Ref(_, ty) => self.check_type(env, ty),
            fhir::Ty::Never
            | fhir::Ty::Param(_)
            | fhir::Ty::Float(_)
            | fhir::Ty::Str
            | fhir::Ty::Char => Ok(()),
        }
    }

    fn check_base_ty(&self, env: &mut Env, bty: &fhir::BaseTy) -> Result<(), ErrorGuaranteed> {
        match bty {
            fhir::BaseTy::Adt(_, substs) => {
                substs
                    .iter()
                    .map(|ty| self.check_type(env, ty))
                    .try_collect_exhaust()
            }
            fhir::BaseTy::Slice(ty) => self.check_type(env, ty),
            fhir::BaseTy::Int(_) | fhir::BaseTy::Uint(_) | fhir::BaseTy::Bool => Ok(()),
        }
    }

    fn check_index(
        &self,
        env: &mut Env,
        idx: &fhir::Index,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match &idx.kind {
            fhir::IndexKind::Single(arg) => self.check_refine_arg(env, arg, expected),
            fhir::IndexKind::Aggregate(def_id, args) => {
                self.check_aggregate(env, *def_id, args, idx.span)?;
                let found = fhir::Sort::Adt(*def_id);
                if &found != expected {
                    return self.emit_err(errors::SortMismatch::new(idx.span, expected, &found));
                }
                Ok(())
            }
        }
    }

    fn check_aggregate(
        &self,
        env: &mut Env,
        def_id: DefId,
        args: &[fhir::RefineArg],
        span: Span,
    ) -> Result<(), ErrorGuaranteed> {
        let sorts = self.map.sorts_of(def_id).unwrap_or(&[]);
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

    fn check_refine_arg(
        &self,
        env: &mut Env,
        arg: &fhir::RefineArg,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        match arg {
            fhir::RefineArg::Expr { expr, .. } => {
                let found = self.synth_expr(env, expr)?;
                if !self.is_coercible(&found, expected) {
                    return self.emit_err(errors::SortMismatch::new(expr.span, expected, &found));
                }
                if !matches!(&expr.kind, fhir::ExprKind::Var(..)) {
                    self.check_param_uses(env, expr, false)?;
                }
                Ok(())
            }
            fhir::RefineArg::Abs(params, body, span) => {
                if let Some(fsort) = self.is_coercible_to_func(expected) {
                    if params.len() != fsort.inputs().len() {
                        return self.emit_err(errors::ParamCountMismatch::new(
                            *span,
                            fsort.inputs().len(),
                            params.len(),
                        ));
                    }
                    env.with_binders(params, fsort.inputs(), |env| {
                        self.check_expr(env, body, fsort.output())?;
                        self.check_param_uses(env, body, true)
                    })
                } else {
                    self.emit_err(errors::UnexpectedFun::new(*span, expected))
                }
            }
        }
    }

    fn check_pred(&self, env: &Env, expr: &fhir::Expr) -> Result<(), ErrorGuaranteed> {
        self.check_expr(env, expr, &fhir::Sort::Bool)?;
        self.check_param_uses(env, expr, true)
    }

    fn check_expr(
        &self,
        env: &Env,
        e: &fhir::Expr,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        let found = self.synth_expr(env, e)?;
        if self.is_coercible(&found, expected) {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(e.span, expected, &found))
        }
    }

    fn check_loc(&self, env: &Env, loc: fhir::Ident) -> Result<(), ErrorGuaranteed> {
        let found = &env[&loc.name];
        if found == &fhir::Sort::Loc {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(loc.source_info.0, &fhir::Sort::Loc, found))
        }
    }

    fn synth_expr(&self, env: &Env, e: &fhir::Expr) -> Result<fhir::Sort, ErrorGuaranteed> {
        match &e.kind {
            fhir::ExprKind::Var(var, ..) => Ok(env[var].clone()),
            fhir::ExprKind::Literal(lit) => Ok(synth_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => self.synth_binary_op(env, *op, e1, e2),
            fhir::ExprKind::UnaryOp(op, e) => self.synth_unary_op(env, *op, e),
            fhir::ExprKind::Const(_, _) => Ok(fhir::Sort::Int), // TODO: generalize const sorts
            fhir::ExprKind::App(f, es) => self.synth_app(env, f, es, e.span),
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                self.check_expr(env, p, &fhir::Sort::Bool)?;
                let sort = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, &sort)?;
                Ok(sort)
            }
            fhir::ExprKind::Dot(var, fld_sym, fld_span) => {
                let sort = &env[var.name];
                if let fhir::Sort::Adt(def_id) = sort {
                    self.map
                        .adt(def_id.expect_local())
                        .field_sort(*fld_sym)
                        .cloned()
                        .ok_or_else(|| {
                            self.sess.emit_err(errors::FieldNotFound::new(
                                self.tcx,
                                self.map,
                                *def_id,
                                (*fld_sym, *fld_span),
                            ))
                        })
                } else {
                    self.emit_err(errors::InvalidPrimitiveDotAccess::new(
                        *var,
                        sort,
                        (*fld_sym, *fld_span),
                    ))
                }
            }
        }
    }

    fn synth_binary_op(
        &self,
        env: &Env,
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
                Ok(fhir::Sort::Bool)
            }
            fhir::BinOp::Lt | fhir::BinOp::Le | fhir::BinOp::Gt | fhir::BinOp::Ge => {
                self.check_expr(env, e1, &fhir::Sort::Int)?;
                self.check_expr(env, e2, &fhir::Sort::Int)?;
                Ok(fhir::Sort::Bool)
            }
            fhir::BinOp::Add
            | fhir::BinOp::Sub
            | fhir::BinOp::Mod
            | fhir::BinOp::Mul
            | fhir::BinOp::Div => {
                self.check_expr(env, e1, &fhir::Sort::Int)?;
                self.check_expr(env, e2, &fhir::Sort::Int)?;
                Ok(fhir::Sort::Int)
            }
        }
    }

    fn synth_unary_op(
        &self,
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

    #[track_caller]
    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R, ErrorGuaranteed> {
        Err(self.sess.emit_err(err))
    }

    fn synth_app(
        &self,
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

    fn synth_func(&self, env: &Env, func: &fhir::Func) -> Result<fhir::FuncSort, ErrorGuaranteed> {
        match func {
            fhir::Func::Var(var) => {
                let sort = &env[&var.name];
                if let Some(fsort) = self.is_coercible_to_func(sort) {
                    Ok(fsort)
                } else {
                    Err(self
                        .sess
                        .emit_err(errors::ExpectedFun::new(var.source_info.0, sort)))
                }
            }
            fhir::Func::Uif(func, span) => {
                Ok(self
                    .map
                    .uif(func)
                    .unwrap_or_else(|| panic!("no definition found for uif `{func:?}` - {span:?}"))
                    .sort
                    .clone())
            }
        }
    }

    /// Whether a value of `sort1` can be automatically coerced to a value of `sort2`. A value of an
    /// [`Adt`] sort with a single field of sort `s` can be coerced to a value of sort `s` and vice
    /// versa, i.e., we can automatically project the field out of the adt or inject a value into the
    /// adt. Note that two adts with a single field of the same sort are not coercible.
    ///
    /// [`Adt`]: fhir::Sort::Adt
    fn is_coercible(&self, sort1: &fhir::Sort, sort2: &fhir::Sort) -> bool {
        if sort1 == sort2 {
            return true;
        }
        if let Some(sort1) = self.is_single_field_adt(sort1) {
            return sort1 == sort2;
        }
        if let Some(sort2) = self.is_single_field_adt(sort2) {
            return sort1 == sort2;
        }

        false
    }

    fn is_coercible_to_func(&self, sort: &fhir::Sort) -> Option<fhir::FuncSort> {
        if let fhir::Sort::Func(fsort) = sort {
            Some(fsort.clone())
        } else if let Some(fhir::Sort::Func(fsort)) = self.is_single_field_adt(sort) {
            Some(fsort.clone())
        } else {
            None
        }
    }

    fn is_single_field_adt(&self, sort: &fhir::Sort) -> Option<&'a fhir::Sort> {
        if let fhir::Sort::Adt(def_id) = sort && let Some([sort]) = self.map.sorts_of(*def_id) {
            Some(sort)
        } else {
            None
        }
    }

    /// Checks that refinement parameters are used in allowed positions.
    fn check_param_uses(
        &self,
        env: &Env,
        expr: &fhir::Expr,
        is_top_level_conj: bool,
    ) -> Result<(), ErrorGuaranteed> {
        match &expr.kind {
            fhir::ExprKind::BinaryOp(bin_op, exprs) => {
                let is_pred = is_top_level_conj && matches!(bin_op, fhir::BinOp::And);
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses(env, e, is_pred))
            }
            fhir::ExprKind::UnaryOp(_, e) => self.check_param_uses(env, e, false),
            fhir::ExprKind::App(func, args) => {
                if !is_top_level_conj
                   && let fhir::Func::Var(var) = func
                   && let fhir::InferMode::KVar = self.modes[&var.name]
                {
                    return self.emit_err(errors::InvalidParamPos::new(var.source_info.0, &env[var.name]));
                }
                args.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses(env, arg, false))
            }
            fhir::ExprKind::Var(name, _, span) => {
                if let sort @ fhir::Sort::Func(_) = &env[name] {
                    return self.emit_err(errors::InvalidParamPos::new(*span, sort));
                }
                Ok(())
            }
            fhir::ExprKind::IfThenElse(exprs) => {
                exprs
                    .iter()
                    .try_for_each_exhaust(|e| self.check_param_uses(env, e, false))
            }
            fhir::ExprKind::Literal(_) | fhir::ExprKind::Const(_, _) => Ok(()),
            fhir::ExprKind::Dot(var, _, _) => {
                if let sort @ fhir::Sort::Func(_) = &env[var.name] {
                    return self.emit_err(errors::InvalidParamPos::new(var.span(), sort));
                }
                Ok(())
            }
        }
    }
}

fn synth_lit(lit: fhir::Lit) -> fhir::Sort {
    match lit {
        fhir::Lit::Int(_) => fhir::Sort::Int,
        fhir::Lit::Bool(_) => fhir::Sort::Bool,
    }
}

mod errors {
    use flux_macros::{Diagnostic, Subdiagnostic};
    use flux_middle::fhir;
    use rustc_errors::MultiSpan;
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{Span, Symbol};

    #[derive(Diagnostic)]
    #[diag(wf::sort_mismatch, code = "FLUX")]
    pub(super) struct SortMismatch<'a> {
        #[primary_span]
        #[label]
        span: Span,
        expected: &'a fhir::Sort,
        found: &'a fhir::Sort,
    }

    impl<'a> SortMismatch<'a> {
        pub(super) fn new(span: Span, expected: &'a fhir::Sort, found: &'a fhir::Sort) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::arg_count_mismatch, code = "FLUX")]
    pub(super) struct ArgCountMismatch {
        #[primary_span]
        #[label]
        span: Option<Span>,
        expected: usize,
        found: usize,
        thing: String,
    }

    impl ArgCountMismatch {
        pub(super) fn new(
            span: Option<Span>,
            thing: String,
            expected: usize,
            found: usize,
        ) -> Self {
            Self { span, expected, found, thing }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::duplicated_ensures, code = "FLUX")]
    pub(super) struct DuplicatedEnsures {
        #[primary_span]
        span: Span,
        loc: Symbol,
    }

    impl DuplicatedEnsures {
        pub(super) fn new(loc: &fhir::Ident) -> DuplicatedEnsures {
            Self { span: loc.source_info.0, loc: loc.source_info.1 }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::missing_ensures, code = "FLUX")]
    pub(super) struct MissingEnsures {
        #[primary_span]
        span: Span,
    }

    impl MissingEnsures {
        pub(super) fn new(loc: &fhir::Ident) -> MissingEnsures {
            Self { span: loc.source_info.0 }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::expected_fun, code = "FLUX")]
    pub(super) struct ExpectedFun<'a> {
        #[primary_span]
        span: Span,
        found: &'a fhir::Sort,
    }

    impl<'a> ExpectedFun<'a> {
        pub(super) fn new(span: Span, found: &'a fhir::Sort) -> Self {
            Self { span, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::invalid_param_in_func_pos, code = "FLUX")]
    pub(super) struct InvalidParamPos<'a> {
        #[primary_span]
        #[label]
        span: Span,
        sort: &'a fhir::Sort,
        is_pred: bool,
    }

    impl<'a> InvalidParamPos<'a> {
        pub(super) fn new(span: Span, sort: &'a fhir::Sort) -> Self {
            Self { span, sort, is_pred: sort.is_pred() }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::unexpected_fun, code = "FLUX")]
    pub(super) struct UnexpectedFun<'a> {
        #[primary_span]
        #[label]
        span: Span,
        sort: &'a fhir::Sort,
    }

    impl<'a> UnexpectedFun<'a> {
        pub(super) fn new(span: Span, sort: &'a fhir::Sort) -> Self {
            Self { span, sort }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::param_count_mismatch, code = "FLUX")]
    pub(super) struct ParamCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        expected: usize,
        found: usize,
    }

    impl ParamCountMismatch {
        pub(super) fn new(span: Span, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::field_not_found, code = "FLUX")]
    pub struct FieldNotFound {
        #[primary_span]
        span: Span,
        fld: Symbol,
        def_kind: &'static str,
        def_name: String,
        #[subdiagnostic]
        def_note: Option<DefSpanNote>,
    }

    impl FieldNotFound {
        pub fn new(tcx: TyCtxt, map: &fhir::Map, def_id: DefId, fld: (Symbol, Span)) -> Self {
            let def_kind = tcx.def_kind(def_id).descr(def_id);
            let def_name = tcx.def_path_str(def_id);
            let def_note = DefSpanNote::new(tcx, map, def_id);
            Self { span: fld.1, fld: fld.0, def_kind, def_name, def_note }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::invalid_primitive_dot_access, code = "FLUX")]
    pub struct InvalidPrimitiveDotAccess<'a> {
        #[primary_span]
        #[label]
        span: Span,
        param_name: Symbol,
        sort: &'a fhir::Sort,
    }

    impl<'a> InvalidPrimitiveDotAccess<'a> {
        pub fn new(var: fhir::Ident, sort: &'a fhir::Sort, fld: (Symbol, Span)) -> Self {
            let span = var.span().to(fld.1);
            Self { sort, span, param_name: var.sym() }
        }
    }

    #[derive(Subdiagnostic)]
    #[note(wf::def_span_note)]
    struct DefSpanNote {
        #[primary_span]
        sp: MultiSpan,
        def_kind: &'static str,
        has_params: bool,
    }

    impl DefSpanNote {
        fn new(tcx: TyCtxt, map: &fhir::Map, def_id: DefId) -> Option<Self> {
            let mut sp = MultiSpan::from_span(tcx.def_ident_span(def_id)?);
            let refined_by = map.refined_by(def_id)?;
            if !refined_by.params.is_empty() {
                sp.push_span_label(refined_by.span, "");
            }
            let def_kind = tcx.def_kind(def_id).descr(def_id);
            Some(Self { sp, def_kind, has_params: !refined_by.params.is_empty() })
        }
    }
}
