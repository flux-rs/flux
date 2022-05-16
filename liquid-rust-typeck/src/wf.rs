use liquid_rust_common::iter::IterExt;
use liquid_rust_core::ty::{self as core, AdtSortsMap};
use rustc_errors::ErrorReported;
use rustc_hash::FxHashMap;
use rustc_session::{Session, SessionDiagnostic};

use crate::{lowering::lower_sort, ty};

pub struct Wf<'a, T> {
    sess: &'a Session,
    adt_sorts: &'a T,
}

struct Env {
    sorts: FxHashMap<core::Name, ty::Sort>,
    bound_var_sorts: Option<Vec<ty::Sort>>,
}

impl Env {
    fn new(params: &[core::Param]) -> Env {
        let sorts = params
            .iter()
            .map(|param| (param.name.name, lower_sort(param.sort)))
            .collect();
        Env { sorts, bound_var_sorts: None }
    }

    fn with_bound_var<R>(&mut self, sorts: Vec<ty::Sort>, f: impl FnOnce(&Self) -> R) -> R {
        self.bound_var_sorts = Some(sorts);
        let r = f(self);
        self.bound_var_sorts = None;
        r
    }
}

impl std::ops::Index<&'_ core::Var> for Env {
    type Output = ty::Sort;

    fn index(&self, var: &core::Var) -> &Self::Output {
        match var {
            core::Var::Bound(idx) => &self.bound_var_sorts.as_ref().unwrap()[*idx as usize],
            core::Var::Free(name) => &self.sorts[name],
        }
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

        self.check_expr(&env, &qualifier.expr, ty::Sort::bool())
    }

    pub fn check_adt_def(&self, def: &core::AdtDef) -> Result<(), ErrorReported> {
        let mut env = Env::new(def.refined_by());
        if let core::AdtDef::Transparent { variants, .. } = def {
            variants
                .iter()
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
            core::Constr::Pred(e) => self.check_expr(env, e, ty::Sort::bool()),
        }
    }

    fn check_type(&self, env: &mut Env, ty: &core::Ty) -> Result<(), ErrorReported> {
        match ty {
            core::Ty::Indexed(bty, refine) => self.check_refine(env, refine, self.sorts(bty)),
            core::Ty::Exists(bty, pred) => {
                env.with_bound_var(self.sorts(bty), |env| {
                    self.check_pred(env, pred, ty::Sort::bool())
                })
            }
            core::Ty::Ptr(loc) => self.check_loc(env, *loc),
            core::Ty::Ref(_, ty) => self.check_type(env, ty),
            core::Ty::Param(_) | core::Ty::Float(_) => Ok(()),
            core::Ty::Tuple(tys) => {
                tys.iter()
                    .try_for_each_exhaust(|ty| self.check_type(env, ty))
            }
        }
    }

    fn check_refine(
        &self,
        env: &Env,
        refine: &core::Indices,
        expected: Vec<ty::Sort>,
    ) -> Result<(), ErrorReported> {
        let found = self.synth_refine(env, refine)?;
        if expected.len() != found.len() {
            return self.emit_err(errors::GenericCountMismatch::new(
                Some(refine.span),
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
                    self.emit_err(errors::SortMismatch::new(Some(refine.span), expected, found))
                }
            })
            .try_collect_exhaust()
    }

    fn check_pred(
        &self,
        env: &Env,
        pred: &core::Pred,
        sort: ty::Sort,
    ) -> Result<(), ErrorReported> {
        match pred {
            core::Pred::Hole => Ok(()),
            core::Pred::Expr(e) => self.check_expr(env, e, sort),
        }
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
        let found = env[&core::Var::Free(loc.name)].clone();
        if found == ty::Sort::loc() {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(
                Some(loc.source_info.0),
                ty::Sort::loc(),
                found,
            ))
        }
    }

    fn synth_refine(
        &self,
        env: &Env,
        refine: &core::Indices,
    ) -> Result<Vec<ty::Sort>, ErrorReported> {
        let sorts: Vec<ty::Sort> = refine
            .exprs
            .iter()
            .map(|e| self.synth_expr(env, e))
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
                self.check_expr(env, e1, ty::Sort::bool())?;
                self.check_expr(env, e2, ty::Sort::bool())?;
                Ok(ty::Sort::bool())
            }
            core::BinOp::Eq => {
                let s = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, s)?;
                Ok(ty::Sort::bool())
            }
            core::BinOp::Lt | core::BinOp::Le | core::BinOp::Gt | core::BinOp::Ge => {
                self.check_expr(env, e1, ty::Sort::int())?;
                self.check_expr(env, e2, ty::Sort::int())?;
                Ok(ty::Sort::bool())
            }
            core::BinOp::Add | core::BinOp::Sub | core::BinOp::Mod | core::BinOp::Mul => {
                self.check_expr(env, e1, ty::Sort::int())?;
                self.check_expr(env, e2, ty::Sort::int())?;
                Ok(ty::Sort::int())
            }
        }
    }

    fn synth_lit(&self, lit: core::Lit) -> ty::Sort {
        match lit {
            core::Lit::Int(_) => ty::Sort::int(),
            core::Lit::Bool(_) => ty::Sort::bool(),
        }
    }

    fn sorts(&self, bty: &core::BaseTy) -> Vec<ty::Sort> {
        match bty {
            core::BaseTy::Int(_) => vec![ty::Sort::int()],
            core::BaseTy::Uint(_) => vec![ty::Sort::int()],
            core::BaseTy::Bool => vec![ty::Sort::bool()],
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
    pub struct GenericCountMismatch {
        #[message = "this type takes {expected} value parameters but {found} were supplied"]
        #[label = "expected `{expected}` value arguments, found `{found}`"]
        pub span: Option<Span>,
        pub expected: usize,
        pub found: usize,
    }

    impl GenericCountMismatch {
        pub fn new(span: Option<Span>, expected: usize, found: usize) -> Self {
            Self { span, expected, found }
        }
    }
}
