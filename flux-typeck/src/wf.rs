use std::iter;

use flux_common::iter::IterExt;
use flux_middle::{core, global_env::GlobalEnv, ty, ty::conv::conv_sort};
use itertools::izip;
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_span::Span;

pub struct Wf<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
}

struct Env {
    sorts: FxHashMap<core::Name, ty::Sort>,
}

impl Env {
    fn new(params: &[core::Param]) -> Env {
        let sorts = params
            .iter()
            .map(|param| (param.name.name, conv_sort(param.sort)))
            .collect();
        Env { sorts }
    }

    fn with_binders<R>(
        &mut self,
        binders: &[core::Ident],
        sorts: &[ty::Sort],
        f: impl FnOnce(&Self) -> R,
    ) -> R {
        debug_assert_eq!(binders.len(), sorts.len());
        for (binder, sort) in iter::zip(binders, sorts) {
            self.sorts.insert(binder.name, sort.clone());
        }
        let r = f(self);
        for binder in binders {
            self.sorts.remove(&binder.name);
        }
        r
    }
}

impl std::ops::Index<&'_ core::Name> for Env {
    type Output = ty::Sort;

    fn index(&self, var: &core::Name) -> &Self::Output {
        self.sorts
            .get(var)
            .unwrap_or_else(|| panic!("no enty found for key: `{var:?}`"))
    }
}

impl<'a, 'tcx> Wf<'a, 'tcx> {
    pub fn new(genv: &'a GlobalEnv<'a, 'tcx>) -> Wf<'a, 'tcx> {
        Wf { genv }
    }

    pub fn check_fn_sig(&self, fn_sig: &core::FnSig) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::new(&fn_sig.params);

        let args = fn_sig
            .args
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty, true));

        let requires = fn_sig
            .requires
            .iter()
            .try_for_each_exhaust(|constr| self.check_constr(&mut env, constr));

        let ensures = fn_sig
            .ensures
            .iter()
            .try_for_each_exhaust(|constr| self.check_constr(&mut env, constr));

        let ret = self.check_type(&mut env, &fn_sig.ret, false);

        args?;
        ret?;
        ensures?;
        requires?;

        Ok(())
    }

    pub fn check_qualifier(&self, qualifier: &core::Qualifier) -> Result<(), ErrorGuaranteed> {
        let env = Env::new(&qualifier.args);

        self.check_expr(&env, &qualifier.expr, ty::Sort::Bool)
    }

    pub fn check_adt_def(&self, adt_def: &core::AdtDef) -> Result<(), ErrorGuaranteed> {
        let env = Env::new(&adt_def.refined_by);
        adt_def
            .invariants
            .iter()
            .try_for_each_exhaust(|invariant| self.check_expr(&env, invariant, ty::Sort::Bool))?;

        Ok(())
    }

    pub fn check_struct_def(
        &self,
        adt_data: &core::AdtDef,
        def: &core::StructDef,
    ) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::new(&adt_data.refined_by);
        if let core::StructKind::Transparent { fields } = &def.kind {
            fields.iter().try_for_each_exhaust(|ty| {
                if let Some(ty) = ty {
                    self.check_type(&mut env, ty, true)
                } else {
                    Ok(())
                }
            })?;
        }
        Ok(())
    }

    pub fn check_enum_def(&self, def: &core::EnumDef) -> Result<(), ErrorGuaranteed> {
        def.variants
            .iter()
            .try_for_each_exhaust(|variant| self.check_variant(variant))
    }

    fn check_variant(&self, variant: &core::VariantDef) -> Result<(), ErrorGuaranteed> {
        let mut env = Env::new(&variant.params);
        let fields = variant
            .fields
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(&mut env, ty, true));
        let indices =
            self.check_indices(&env, &variant.ret.indices, self.sorts(&variant.ret.bty), false);
        (fields?, indices?);
        Ok(())
    }

    fn check_constr(
        &self,
        env: &mut Env,
        constr: &core::Constraint,
    ) -> Result<(), ErrorGuaranteed> {
        match constr {
            core::Constraint::Type(loc, ty) => {
                [self.check_loc(env, *loc), self.check_type(env, ty, true)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            core::Constraint::Pred(e) => self.check_expr(env, e, ty::Sort::Bool),
        }
    }

    fn check_type(
        &self,
        env: &mut Env,
        ty: &core::Ty,
        allow_binder: bool,
    ) -> Result<(), ErrorGuaranteed> {
        match ty {
            core::Ty::BaseTy(bty) => self.check_base_ty(env, bty, allow_binder),
            core::Ty::Indexed(bty, refine) => {
                self.check_indices(env, refine, self.sorts(bty), allow_binder)?;
                self.check_base_ty(env, bty, allow_binder)
            }
            core::Ty::Exists(bty, binders, pred) => {
                let sorts = self.sorts(bty);
                if binders.len() != sorts.len() {
                    return self.emit_err(errors::ParamCountMismatch::new(
                        None,
                        sorts.len(),
                        binders.len(),
                    ));
                }
                self.check_base_ty(env, bty, allow_binder)?;
                env.with_binders(binders, &sorts, |env| self.check_expr(env, pred, ty::Sort::Bool))
            }
            core::Ty::Ptr(loc) => self.check_loc(env, *loc),
            core::Ty::Ref(_, ty) => self.check_type(env, ty, allow_binder),
            core::Ty::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(env, ty, allow_binder))
            }
            core::Ty::Constr(pred, ty) => {
                self.check_expr(env, pred, ty::Sort::Bool)?;
                self.check_type(env, ty, allow_binder)
            }
            core::Ty::Slice(ty) | core::Ty::Array(ty, _) => self.check_type(env, ty, false),
            core::Ty::Never | core::Ty::Param(_) | core::Ty::Float(_) => Ok(()),
        }
    }

    fn is_box(&self, def_id: DefId) -> bool {
        self.genv.tcx.adt_def(def_id).is_box()
    }

    fn check_base_ty(
        &self,
        env: &mut Env,
        bty: &core::BaseTy,
        allow_binder: bool,
    ) -> Result<(), ErrorGuaranteed> {
        match bty {
            core::BaseTy::Adt(def, substs) => {
                let allow_binder = allow_binder && self.is_box(*def);
                substs
                    .iter()
                    .map(|ty| self.check_type(env, ty, allow_binder))
                    .try_collect_exhaust()
            }
            core::BaseTy::Int(_) | core::BaseTy::Uint(_) | core::BaseTy::Bool => Ok(()),
        }
    }

    fn check_indices(
        &self,
        env: &Env,
        indices: &core::Indices,
        expected: Vec<ty::Sort>,
        allow_binder: bool,
    ) -> Result<(), ErrorGuaranteed> {
        if !allow_binder && indices.indices.iter().any(|i| i.is_binder) {
            return self.emit_err(errors::IllegalBinder::new(Some(indices.span)));
        }

        let found = self.synt_indices(env, indices)?;
        if expected.len() != found.len() {
            return self.emit_err(errors::ParamCountMismatch::new(
                Some(indices.span),
                expected.len(),
                found.len(),
            ));
        }
        izip!(indices, expected, found)
            .map(|(idx, expected, found)| {
                if found == expected {
                    Ok(())
                } else {
                    self.emit_err(errors::SortMismatch::new(idx.expr.span, expected, found))
                }
            })
            .try_collect_exhaust()
    }

    fn check_expr(
        &self,
        env: &Env,
        e: &core::Expr,
        expected: ty::Sort,
    ) -> Result<(), ErrorGuaranteed> {
        let found = self.synth_expr(env, e)?;
        if found == expected {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(e.span, expected, found))
        }
    }

    fn check_loc(&self, env: &Env, loc: core::Ident) -> Result<(), ErrorGuaranteed> {
        let found = env[&loc.name].clone();
        if found == ty::Sort::Loc {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(loc.source_info.0, ty::Sort::Loc, found))
        }
    }

    fn synt_indices(
        &self,
        env: &Env,
        refine: &core::Indices,
    ) -> Result<Vec<ty::Sort>, ErrorGuaranteed> {
        let sorts: Vec<ty::Sort> = refine
            .indices
            .iter()
            .map(|idx| self.synth_expr(env, &idx.expr))
            .try_collect_exhaust()?;
        Ok(sorts)
    }

    fn synth_expr(&self, env: &Env, e: &core::Expr) -> Result<ty::Sort, ErrorGuaranteed> {
        match &e.kind {
            core::ExprKind::Var(var, ..) => Ok(env[var].clone()),
            core::ExprKind::Literal(lit) => Ok(synth_lit(*lit)),
            core::ExprKind::BinaryOp(op, e1, e2) => self.synth_binary_op(env, *op, e1, e2),
            core::ExprKind::Const(_, _) => Ok(ty::Sort::Int), // TODO: generalize const sorts
            core::ExprKind::App(f, es) => self.synth_uf_app(env, f, es, e.span),
            core::ExprKind::IfThenElse(p, e1, e2) => {
                self.check_expr(env, p, ty::Sort::Bool)?;
                let sort = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, sort.clone())?;
                Ok(sort)
            }
        }
    }

    fn synth_binary_op(
        &self,
        env: &Env,
        op: core::BinOp,
        e1: &core::Expr,
        e2: &core::Expr,
    ) -> Result<ty::Sort, ErrorGuaranteed> {
        match op {
            core::BinOp::Or | core::BinOp::And | core::BinOp::Iff | core::BinOp::Imp => {
                self.check_expr(env, e1, ty::Sort::Bool)?;
                self.check_expr(env, e2, ty::Sort::Bool)?;
                Ok(ty::Sort::Bool)
            }
            core::BinOp::Eq | core::BinOp::Ne => {
                let s = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, s)?;
                Ok(ty::Sort::Bool)
            }
            core::BinOp::Lt | core::BinOp::Le | core::BinOp::Gt | core::BinOp::Ge => {
                self.check_expr(env, e1, ty::Sort::Int)?;
                self.check_expr(env, e2, ty::Sort::Int)?;
                Ok(ty::Sort::Bool)
            }
            core::BinOp::Add
            | core::BinOp::Sub
            | core::BinOp::Mod
            | core::BinOp::Mul
            | core::BinOp::Div => {
                self.check_expr(env, e1, ty::Sort::Int)?;
                self.check_expr(env, e2, ty::Sort::Int)?;
                Ok(ty::Sort::Int)
            }
        }
    }

    fn sorts(&self, bty: &core::BaseTy) -> Vec<ty::Sort> {
        match bty {
            core::BaseTy::Int(_) | core::BaseTy::Uint(_) => vec![ty::Sort::Int],
            core::BaseTy::Bool => vec![ty::Sort::Bool],
            core::BaseTy::Adt(def_id, _) => self.genv.adt_def(*def_id).sorts().to_vec(),
        }
    }

    fn emit_err<'b, R>(&'b self, err: impl IntoDiagnostic<'b>) -> Result<R, ErrorGuaranteed> {
        Err(self.genv.sess.emit_err(err))
    }

    fn synth_uf_app(
        &self,
        env: &Env,
        f: &core::UFun,
        es: &[core::Expr],
        span: Span,
    ) -> Result<ty::Sort, ErrorGuaranteed> {
        let Some(uf_def) = self.genv.uf_sorts.get(&f.symbol) else {
            return self.emit_err(errors::UnresolvedFunction::new(f.span));
        };
        let found = es.len();
        let expected = uf_def.inputs.len();
        if expected != found {
            return self.emit_err(errors::ParamCountMismatch::new(Some(span), expected, found));
        }
        for (e, t) in iter::zip(es, &uf_def.inputs) {
            let e_t = self.synth_expr(env, e)?;
            if e_t != *t {
                return self.emit_err(errors::SortMismatch::new(e.span, t.clone(), e_t));
            }
        }
        Ok(uf_def.output.clone())
    }
}

fn synth_lit(lit: core::Lit) -> ty::Sort {
    match lit {
        core::Lit::Int(_) => ty::Sort::Int,
        core::Lit::Bool(_) => ty::Sort::Bool,
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_span::Span;

    use crate::ty;

    #[derive(Diagnostic)]
    #[diag(wf::sort_mismatch, code = "FLUX")]
    pub struct SortMismatch {
        #[primary_span]
        #[label]
        pub span: Span,
        pub expected: ty::Sort,
        pub found: ty::Sort,
    }

    impl SortMismatch {
        pub fn new(span: Span, expected: ty::Sort, found: ty::Sort) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::param_count_mismatch, code = "FLUX")]
    pub struct ParamCountMismatch {
        #[primary_span]
        #[label]
        pub span: Option<Span>,
        pub expected: usize,
        pub found: usize,
    }

    impl ParamCountMismatch {
        pub fn new(span: Option<Span>, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::unresolved_function, code = "FLUX")]
    pub struct UnresolvedFunction {
        #[primary_span]
        #[label]
        pub span: Span,
    }

    impl UnresolvedFunction {
        pub fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(wf::illegal_binder, code = "FLUX")]
    pub struct IllegalBinder {
        #[primary_span]
        #[label]
        pub span: Option<Span>,
    }

    impl IllegalBinder {
        pub fn new(span: Option<Span>) -> Self {
            Self { span }
        }
    }
}
