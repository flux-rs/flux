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
use rustc_span::Span;

pub struct Wf<'a> {
    sess: &'a FluxSession,
    map: &'a fhir::Map,
}

struct Env<'a> {
    sorts: FxHashMap<fhir::Name, &'a fhir::Sort>,
}

impl<'a> Env<'a> {
    fn new(params: &'a [fhir::RefineParam]) -> Env {
        let sorts = params
            .iter()
            .map(|param| (param.name.name, &param.sort))
            .collect();
        Env { sorts }
    }

    fn with_binders<R>(
        &mut self,
        binders: &[fhir::Name],
        sorts: &'a [fhir::Sort],
        f: impl FnOnce(&Self) -> R,
    ) -> R {
        debug_assert_eq!(binders.len(), sorts.len());
        for (binder, sort) in iter::zip(binders, sorts) {
            self.sorts.insert(*binder, sort);
        }
        let r = f(self);
        for binder in binders {
            self.sorts.remove(binder);
        }
        r
    }
}

impl<'a, T: Borrow<fhir::Name>> std::ops::Index<T> for Env<'a> {
    type Output = &'a fhir::Sort;

    fn index(&self, var: T) -> &Self::Output {
        self.sorts
            .get(var.borrow())
            .unwrap_or_else(|| panic!("no enty found for key: `{:?}`", var.borrow()))
    }
}

impl<'a> Wf<'a> {
    pub fn new(sess: &'a FluxSession, map: &'a fhir::Map) -> Wf<'a> {
        Wf { sess, map }
    }

    pub fn check_qualifier(&self, qualifier: &fhir::Qualifier) -> Result<(), ErrorGuaranteed> {
        let env = Env::new(&qualifier.args);

        self.check_expr(&env, &qualifier.expr, &fhir::Sort::Bool)
    }

    pub fn check_adt_def(&self, adt_def: &fhir::AdtDef) -> Result<(), ErrorGuaranteed> {
        let env = Env::new(&adt_def.refined_by.params);
        adt_def
            .invariants
            .iter()
            .try_for_each_exhaust(|invariant| {
                self.check_expr(&env, invariant, &fhir::Sort::Bool)
            })?;

        Ok(())
    }

    pub fn check_fn_sig(&self, fn_sig: &fhir::FnSig) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::new(&fn_sig.params);

        let args = fn_sig
            .args
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty));

        let requires = fn_sig
            .requires
            .iter()
            .try_for_each_exhaust(|constr| self.check_constr(&mut env, constr));

        let ensures = fn_sig
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| self.check_constr(&mut env, constr));

        let ret = self.check_type(&mut env, &fn_sig.ret);

        let constrs = self.check_constrs(fn_sig);

        args?;
        ret?;
        ensures?;
        requires?;
        constrs?;

        Ok(())
    }

    pub fn check_struct_def(
        &self,
        refined_by: &fhir::RefinedBy,
        def: &fhir::StructDef,
    ) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::new(&refined_by.params);
        if let fhir::StructKind::Transparent { fields } = &def.kind {
            fields.iter().try_for_each_exhaust(|ty| {
                if let Some(ty) = ty {
                    self.check_type(&mut env, ty)
                } else {
                    Ok(())
                }
            })?;
        }
        Ok(())
    }

    pub fn check_enum_def(&self, def: &fhir::EnumDef) -> Result<(), ErrorGuaranteed> {
        def.variants
            .iter()
            .try_for_each_exhaust(|variant| self.check_variant(variant))
    }

    fn check_variant(&self, variant: &fhir::VariantDef) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::new(&variant.params);
        let fields = variant
            .fields
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty));
        let indices = self.check_indices(&env, &variant.ret.indices, self.sorts(&variant.ret.bty));
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
        env: &mut Env<'a>,
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

    fn check_type(&self, env: &mut Env<'a>, ty: &fhir::Ty) -> Result<(), ErrorGuaranteed> {
        match ty {
            fhir::Ty::BaseTy(bty) => self.check_base_ty(env, bty),
            fhir::Ty::Indexed(bty, refine) => {
                self.check_indices(env, refine, self.sorts(bty))?;
                self.check_base_ty(env, bty)
            }
            fhir::Ty::Exists(bty, binders, pred) => {
                let sorts = self.sorts(bty);
                if binders.len() != sorts.len() {
                    return self.emit_err(errors::ParamCountMismatch::new(
                        None,
                        sorts.len(),
                        binders.len(),
                    ));
                }
                self.check_base_ty(env, bty)?;
                env.with_binders(binders, sorts, |env| self.check_pred(env, pred))
            }
            fhir::Ty::Ptr(loc) => self.check_loc(env, *loc),
            fhir::Ty::Ref(_, ty) => self.check_type(env, ty),
            fhir::Ty::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(env, ty))
            }
            fhir::Ty::Constr(pred, ty) => {
                self.check_pred(env, pred)?;
                self.check_type(env, ty)
            }
            fhir::Ty::Slice(ty) | fhir::Ty::Array(ty, _) => self.check_type(env, ty),
            fhir::Ty::Never
            | fhir::Ty::Param(_)
            | fhir::Ty::Float(_)
            | fhir::Ty::Str
            | fhir::Ty::Char => Ok(()),
        }
    }

    fn check_base_ty(&self, env: &mut Env<'a>, bty: &fhir::BaseTy) -> Result<(), ErrorGuaranteed> {
        match bty {
            fhir::BaseTy::Adt(_, substs) => {
                substs
                    .iter()
                    .map(|ty| self.check_type(env, ty))
                    .try_collect_exhaust()
            }
            fhir::BaseTy::Int(_) | fhir::BaseTy::Uint(_) | fhir::BaseTy::Bool => Ok(()),
        }
    }

    fn check_indices(
        &self,
        env: &Env,
        indices: &fhir::Indices,
        expected: &[fhir::Sort],
    ) -> Result<(), ErrorGuaranteed> {
        if expected.len() != indices.indices.len() {
            return self.emit_err(errors::ParamCountMismatch::new(
                Some(indices.span),
                expected.len(),
                indices.indices.len(),
            ));
        }
        izip!(indices, expected)
            .map(|(idx, expected)| self.check_index(env, idx, expected))
            .try_collect_exhaust()
    }

    fn check_index(
        &self,
        env: &Env,
        idx: &fhir::Index,
        expected: &fhir::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        let found = self.synth_expr(env, &idx.expr)?;
        if found != expected {
            return self.emit_err(errors::SortMismatch::new(idx.expr.span, expected, found));
        }
        self.check_param_uses(env, &idx.expr, false)
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
        if found == expected {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(e.span, expected, found))
        }
    }

    fn check_loc(&self, env: &Env, loc: fhir::Ident) -> Result<(), ErrorGuaranteed> {
        let found = env[&loc.name];
        if found == &fhir::Sort::Loc {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(loc.source_info.0, &fhir::Sort::Loc, found))
        }
    }

    fn synth_expr(&self, env: &Env<'a>, e: &'a fhir::Expr) -> Result<&fhir::Sort, ErrorGuaranteed> {
        match &e.kind {
            fhir::ExprKind::Var(var, ..) => Ok(env[var]),
            fhir::ExprKind::Literal(lit) => Ok(synth_lit(*lit)),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => self.synth_binary_op(env, *op, e1, e2),
            fhir::ExprKind::Const(_, _) => Ok(&fhir::Sort::Int), // TODO: generalize const sorts
            fhir::ExprKind::App(f, es) => self.synth_app(env, f, es, e.span),
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                self.check_expr(env, p, &fhir::Sort::Bool)?;
                let sort = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, sort)?;
                Ok(sort)
            }
        }
    }

    fn synth_binary_op(
        &self,
        env: &Env<'a>,
        op: fhir::BinOp,
        e1: &fhir::Expr,
        e2: &fhir::Expr,
    ) -> Result<&'a fhir::Sort, ErrorGuaranteed> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                self.check_expr(env, e1, &fhir::Sort::Bool)?;
                self.check_expr(env, e2, &fhir::Sort::Bool)?;
                Ok(&fhir::Sort::Bool)
            }
            fhir::BinOp::Eq | fhir::BinOp::Ne => {
                let s = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, s)?;
                Ok(&fhir::Sort::Bool)
            }
            fhir::BinOp::Lt | fhir::BinOp::Le | fhir::BinOp::Gt | fhir::BinOp::Ge => {
                self.check_expr(env, e1, &fhir::Sort::Int)?;
                self.check_expr(env, e2, &fhir::Sort::Int)?;
                Ok(&fhir::Sort::Bool)
            }
            fhir::BinOp::Add
            | fhir::BinOp::Sub
            | fhir::BinOp::Mod
            | fhir::BinOp::Mul
            | fhir::BinOp::Div => {
                self.check_expr(env, e1, &fhir::Sort::Int)?;
                self.check_expr(env, e2, &fhir::Sort::Int)?;
                Ok(&fhir::Sort::Int)
            }
        }
    }

    fn sorts(&self, bty: &fhir::BaseTy) -> &'a [fhir::Sort] {
        match bty {
            fhir::BaseTy::Int(_) | fhir::BaseTy::Uint(_) => &[fhir::Sort::Int],
            fhir::BaseTy::Bool => &[fhir::Sort::Bool],
            fhir::BaseTy::Adt(def_id, _) => self.map.sorts(*def_id).unwrap_or_default(),
        }
    }

    #[track_caller]
    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R, ErrorGuaranteed> {
        Err(self.sess.emit_err(err))
    }

    fn synth_app(
        &self,
        env: &Env<'a>,
        func: &fhir::Func,
        args: &[fhir::Expr],
        span: Span,
    ) -> Result<&fhir::Sort, ErrorGuaranteed> {
        let fsort = self.synth_func(env, func)?;
        if args.len() != fsort.inputs().len() {
            return self.emit_err(errors::ParamCountMismatch::new(
                Some(span),
                fsort.inputs().len(),
                args.len(),
            ));
        }

        iter::zip(args, fsort.inputs())
            .try_for_each_exhaust(|(arg, formal)| self.check_expr(env, arg, formal))?;

        Ok(fsort.output())
    }

    fn synth_func(
        &self,
        env: &Env<'a>,
        func: &fhir::Func,
    ) -> Result<&fhir::FuncSort, ErrorGuaranteed> {
        match func {
            fhir::Func::Var(var) => {
                match env[&var.name] {
                    fhir::Sort::Func(sort) => Ok(sort),
                    sort => {
                        Err(self
                            .sess
                            .emit_err(errors::ExpectedFun::new(var.source_info.0, sort)))
                    }
                }
            }
            fhir::Func::Uif(func, span) => {
                Ok(&self
                    .map
                    .uif(func)
                    .unwrap_or_else(|| panic!("no definition found for uif `{func:?}` - {span:?}"))
                    .sort)
            }
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
            fhir::ExprKind::App(func, args) => {
                if !is_top_level_conj && let fhir::Func::Var(var) = func {
                    return self.emit_err(errors::InvalidParamPos::new(var.source_info.0, env[var.name]));
                }
                args.iter()
                    .try_for_each_exhaust(|arg| self.check_param_uses(env, arg, false))
            }
            fhir::ExprKind::Var(name, _, span) => {
                if let sort @ fhir::Sort::Func(_) = env[name] {
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
        }
    }
}

fn synth_lit(lit: fhir::Lit) -> &'static fhir::Sort {
    match lit {
        fhir::Lit::Int(_) => &fhir::Sort::Int,
        fhir::Lit::Bool(_) => &fhir::Sort::Bool,
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::fhir;
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
    #[diag(wf::param_count_mismatch, code = "FLUX")]
    pub(super) struct ParamCountMismatch {
        #[primary_span]
        #[label]
        span: Option<Span>,
        expected: usize,
        found: usize,
    }

    impl ParamCountMismatch {
        pub(super) fn new(span: Option<Span>, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
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
}
