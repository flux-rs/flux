use liquid_rust_common::{errors::ErrorReported, iter::IterExt};
use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;
use rustc_session::{Session, SessionDiagnostic};

use crate::{global_env::AdtDefs, lowering::lower_sort, ty};

pub struct Wf<'a> {
    sess: &'a Session,
    adt_defs: &'a AdtDefs,
}

type Env = FxHashMap<core::Var, ty::Sort>;

impl Wf<'_> {
    pub fn new<'a>(sess: &'a Session, adt_defs: &'a AdtDefs) -> Wf<'a> {
        Wf { sess, adt_defs }
    }

    pub fn check_fn_sig(&self, fn_sig: &core::FnSig) -> Result<(), ErrorReported> {
        let mut env = Env::default();
        let params = fn_sig
            .params
            .iter()
            .map(|param| {
                env.insert(core::Var::Free(param.name.name), lower_sort(param.sort));
                self.check_expr(&env, &param.pred, ty::Sort::bool())
            })
            .try_collect_exhaust();

        let args = fn_sig
            .args
            .iter()
            .map(|ty| self.check_type(&mut env, ty))
            .try_collect_exhaust();

        let ensures = fn_sig
            .ensures
            .iter()
            .map(|(_, ty)| self.check_type(&mut env, ty))
            .try_collect_exhaust();

        let ret = self.check_type(&mut env, &fn_sig.ret);

        args?;
        ret?;
        params?;
        ensures?;

        Ok(())
    }

    fn check_type(&self, env: &mut Env, ty: &core::Ty) -> Result<(), ErrorReported> {
        match ty {
            core::Ty::Refine(bty, refine) => self.check_refine(env, refine, self.sort(bty)),
            core::Ty::Exists(bty, pred) => {
                env.insert(core::Var::Bound, self.sort(bty));
                self.check_pred(env, pred, ty::Sort::bool())
            }
            core::Ty::StrgRef(_) => {
                // TODO: check identifier is actually a region
                Ok(())
            }
            core::Ty::WeakRef(ty) | core::Ty::ShrRef(ty) => self.check_type(env, ty),
            core::Ty::Param(_) => Ok(()),
        }
    }

    fn check_refine(
        &self,
        env: &mut Env,
        refine: &core::Refine,
        expected: ty::Sort,
    ) -> Result<(), ErrorReported> {
        let found = self.synth_refine(env, refine)?;
        if found == expected {
            Ok(())
        } else {
            self.emit_err(errors::SortMismatch::new(Some(refine.span), found, expected))
        }
    }

    fn check_pred(
        &self,
        env: &Env,
        pred: &core::Pred,
        sort: ty::Sort,
    ) -> Result<(), ErrorReported> {
        match pred {
            core::Pred::Infer => Ok(()),
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

    fn synth_refine(&self, env: &Env, refine: &core::Refine) -> Result<ty::Sort, ErrorReported> {
        let sorts: Vec<ty::Sort> = refine
            .exprs
            .iter()
            .map(|e| self.synth_expr(env, e))
            .try_collect_exhaust()?;
        Ok(ty::Sort::tuple(sorts))
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
            core::BinOp::Add | core::BinOp::Sub | core::BinOp::Mod => {
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

    fn sort(&self, bty: &core::BaseTy) -> ty::Sort {
        match bty {
            core::BaseTy::Int(_) => ty::Sort::int(),
            core::BaseTy::Uint(_) => ty::Sort::int(),
            core::BaseTy::Bool => ty::Sort::bool(),
            core::BaseTy::Adt(def_id, _) => {
                if let Some(def) = self.adt_defs.get(*def_id) {
                    ty::Sort::tuple(def.refined_by.iter().map(|param| param.sort.clone()))
                } else {
                    ty::Sort::unit()
                }
            }
        }
    }

    fn emit_err<'a, T>(&'a self, err: impl SessionDiagnostic<'a>) -> Result<T, ErrorReported> {
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
}
