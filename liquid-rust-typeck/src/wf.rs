use std::iter;

use liquid_rust_common::iter::IterExt;
use liquid_rust_middle::core::{self, AdtSortsMap};
use rustc_errors::ErrorReported;
use rustc_hash::FxHashMap;
use rustc_session::{Session, SessionDiagnostic};

use liquid_rust_middle::{ty, ty::lowering::lower_sort};

pub struct Wf<'a, T> {
    sess: &'a Session,
    adt_sorts: &'a T,
}

struct Env {
    sorts: FxHashMap<core::Name, ty::Sort>,
}

impl Env {
    fn new(params: &[core::Param]) -> Env {
        let sorts = params
            .iter()
            .map(|param| (param.name.name, lower_sort(param.sort)))
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
        &self.sorts[var]
    }
}

impl<T: AdtSortsMap> Wf<'_, T> {
    pub fn new<'a>(sess: &'a Session, refined_by: &'a T) -> Wf<'a, T> {
        Wf { sess, adt_sorts: refined_by }
    }

    pub fn check_fn_sig(&self, fn_sig: &core::FnSig) -> Result<(), ErrorReported> {
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

        args?;
        ret?;
        ensures?;
        requires?;

        Ok(())
    }

    pub fn check_qualifier(&self, qualifier: &core::Qualifier) -> Result<(), ErrorReported> {
        let env = Env::new(&qualifier.args);

        self.check_expr(&env, &qualifier.expr, ty::Sort::Bool)
    }

    pub fn check_adt_def(&self, def: &core::AdtDef) -> Result<(), ErrorReported> {
        let mut env = Env::new(&def.refined_by);
        if let core::AdtDefKind::Transparent { variants, .. } = &def.kind {
            variants
                .iter()
                .flatten()
                .flatten()
                .try_for_each_exhaust(|variant| self.check_variant_def(&mut env, variant))?;
        }
        Ok(())
    }

    fn check_variant_def(
        &self,
        env: &mut Env,
        variant: &core::VariantDef,
    ) -> Result<(), ErrorReported> {
        variant
            .fields
            .iter()
            .try_for_each_exhaust(|ty| self.check_type(env, ty))
    }

    fn check_constr(&self, env: &mut Env, constr: &core::Constr) -> Result<(), ErrorReported> {
        match constr {
            core::Constr::Type(loc, ty) => {
                [self.check_loc(env, *loc), self.check_type(env, ty)]
                    .into_iter()
                    .try_collect_exhaust()
            }
            core::Constr::Pred(e) => self.check_expr(env, e, ty::Sort::Bool),
        }
    }

    fn check_type(&self, env: &mut Env, ty: &core::Ty) -> Result<(), ErrorReported> {
        match ty {
            core::Ty::BaseTy(bty) => self.check_base_ty(env, bty),
            core::Ty::Indexed(bty, refine) => {
                self.check_indices(env, refine, self.sorts(bty))?;
                self.check_base_ty(env, bty)
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
                self.check_base_ty(env, bty)?;
                env.with_binders(binders, &sorts, |env| self.check_expr(env, pred, ty::Sort::Bool))
            }
            core::Ty::Ptr(loc) => self.check_loc(env, *loc),
            core::Ty::Ref(_, ty) => self.check_type(env, ty),
            core::Ty::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(env, ty))
            }
            core::Ty::Never | core::Ty::Param(_) | core::Ty::Float(_) => Ok(()),
        }
    }

    fn check_base_ty(&self, env: &mut Env, bty: &core::BaseTy) -> Result<(), ErrorReported> {
        match bty {
            core::BaseTy::Adt(_, substs) => {
                substs
                    .iter()
                    .map(|ty| self.check_type(env, ty))
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
    ) -> Result<(), ErrorReported> {
        let found = self.synt_indices(env, indices)?;
        if expected.len() != found.len() {
            return self.emit_err(errors::ParamCountMismatch::new(
                Some(indices.span),
                expected.len(),
                found.len(),
            ));
        }
        expected
            .into_iter()
            .zip(found)
            .map(|(expected, found)| {
                if found == expected {
                    Ok(())
                } else {
                    self.emit_err(errors::SortMismatch::new(Some(indices.span), expected, found))
                }
            })
            .try_collect_exhaust()
    }

    fn check_expr(
        &self,
        env: &Env,
        e: &core::Expr,
        expected: ty::Sort,
    ) -> Result<(), ErrorReported> {
        let found = self.synth_expr(env, e)?;
        if found == expected {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(e.span, expected, found))
        }
    }

    fn check_loc(&self, env: &Env, loc: core::Ident) -> Result<(), ErrorReported> {
        let found = env[&loc.name].clone();
        if found == ty::Sort::Loc {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(Some(loc.source_info.0), ty::Sort::Loc, found))
        }
    }

    fn synt_indices(
        &self,
        env: &Env,
        refine: &core::Indices,
    ) -> Result<Vec<ty::Sort>, ErrorReported> {
        let sorts: Vec<ty::Sort> = refine
            .indices
            .iter()
            .map(|idx| self.synth_expr(env, &idx.expr))
            .try_collect_exhaust()?;
        Ok(sorts)
    }

    fn synth_expr(&self, env: &Env, e: &core::Expr) -> Result<ty::Sort, ErrorReported> {
        match &e.kind {
            core::ExprKind::Var(var, ..) => Ok(env[var].clone()),
            core::ExprKind::Literal(lit) => Ok(self.synth_lit(*lit)),
            core::ExprKind::BinaryOp(op, e1, e2) => self.synth_binary_op(env, *op, e1, e2),
        }
    }

    fn synth_binary_op(
        &self,
        env: &Env,
        op: core::BinOp,
        e1: &core::Expr,
        e2: &core::Expr,
    ) -> Result<ty::Sort, ErrorReported> {
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

    fn synth_lit(&self, lit: core::Lit) -> ty::Sort {
        match lit {
            core::Lit::Int(_) => ty::Sort::Int,
            core::Lit::Bool(_) => ty::Sort::Bool,
        }
    }

    fn sorts(&self, bty: &core::BaseTy) -> Vec<ty::Sort> {
        match bty {
            core::BaseTy::Int(_) => vec![ty::Sort::Int],
            core::BaseTy::Uint(_) => vec![ty::Sort::Int],
            core::BaseTy::Bool => vec![ty::Sort::Bool],
            core::BaseTy::Adt(def_id, _) => {
                if let Some(params) = self.adt_sorts.get(*def_id) {
                    params.iter().map(|sort| lower_sort(*sort)).collect()
                } else {
                    vec![]
                }
            }
        }
    }

    fn emit_err<'a, R>(&'a self, err: impl SessionDiagnostic<'a>) -> Result<R, ErrorReported> {
        self.sess.emit_err(err);
        Err(ErrorReported)
    }
}

mod errors {
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    use crate::ty;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct SortMismatch {
        #[message = "mismatched sorts"]
        #[label = "expected `{expected}`, found `{found}`"]
        pub span: Option<Span>,
        pub expected: ty::Sort,
        pub found: ty::Sort,
    }

    impl SortMismatch {
        pub fn new(span: Option<Span>, expected: ty::Sort, found: ty::Sort) -> Self {
            Self { span, expected, found }
        }
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct ParamCountMismatch {
        #[message = "this type takes {expected} refinement parameters but {found} were supplied"]
        #[label = "expected `{expected}` refinement arguments, found `{found}`"]
        pub span: Option<Span>,
        pub expected: usize,
        pub found: usize,
    }

    impl ParamCountMismatch {
        pub fn new(span: Option<Span>, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
        }
    }
}
