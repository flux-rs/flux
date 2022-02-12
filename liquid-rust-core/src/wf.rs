use liquid_rust_common::{errors::ErrorReported, iter::IterExt};
use rustc_hash::FxHashMap;
use rustc_session::{Session, SessionDiagnostic};

use crate::ty::{BinOp, Expr, ExprKind, FnSig, Pred, Sort, Ty, Var};

pub struct Wf<'a> {
    sess: &'a Session,
}

impl Wf<'_> {
    pub fn new(sess: &Session) -> Wf {
        Wf { sess }
    }

    pub fn check_fn_sig(&self, fn_sig: &FnSig) -> Result<(), ErrorReported> {
        let mut env = Env::default();
        let params = fn_sig
            .params
            .iter()
            .map(|param| {
                env.insert(Var::Free(param.name.name), param.sort);
                self.check_expr(&env, &param.pred, Sort::Bool)
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

    fn check_type(&self, env: &mut Env, ty: &Ty) -> Result<(), ErrorReported> {
        match ty {
            Ty::Refine(bty, e) => self.check_expr(env, e, bty.sort()),
            Ty::Exists(bty, pred) => {
                env.insert(Var::Bound, bty.sort());
                self.check_pred(env, pred, Sort::Bool)
            }
            Ty::StrgRef(_) => {
                // TODO: check identifier is actually a region
                Ok(())
            }
            Ty::WeakRef(ty) | Ty::ShrRef(ty) => self.check_type(env, ty),
            Ty::Param(_) => Ok(()),
        }
    }

    fn check_pred(&self, env: &Env, pred: &Pred, sort: Sort) -> Result<(), ErrorReported> {
        match pred {
            Pred::Infer => Ok(()),
            Pred::Expr(e) => self.check_expr(env, e, sort),
        }
    }

    fn check_expr(&self, env: &Env, e: &Expr, expected: Sort) -> Result<(), ErrorReported> {
        let found = self.synth_expr(env, e)?;
        if found != expected {
            self.emit_err(errors::SortMismatch::new(e.span, expected, found))
        } else {
            Ok(())
        }
    }

    fn synth_expr(&self, env: &Env, e: &Expr) -> Result<Sort, ErrorReported> {
        match &e.kind {
            ExprKind::Var(var, ..) => Ok(env[var]),
            ExprKind::Literal(lit) => Ok(lit.sort()),
            ExprKind::BinaryOp(op, e1, e2) => self.synth_binary_op(env, *op, e1, e2),
        }
    }

    fn synth_binary_op(
        &self,
        env: &Env,
        op: BinOp,
        e1: &Expr,
        e2: &Expr,
    ) -> Result<Sort, ErrorReported> {
        match op {
            BinOp::Iff | BinOp::Imp => {
                self.check_expr(env, e1, Sort::Bool)?;
                self.check_expr(env, e2, Sort::Bool)?;
                Ok(Sort::Bool)
            }
            BinOp::Eq => {
                let s = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, s)?;
                Ok(Sort::Bool)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.check_expr(env, e1, Sort::Int)?;
                self.check_expr(env, e2, Sort::Int)?;
                Ok(Sort::Bool)
            }
            BinOp::Add | BinOp::Sub => {
                self.check_expr(env, e1, Sort::Int)?;
                self.check_expr(env, e2, Sort::Int)?;
                Ok(Sort::Int)
            }
            BinOp::Mod => {
                self.check_expr(env, e1, Sort::Int)?;
                self.check_expr(env, e2, Sort::Int)?;
                Ok(Sort::Int)
            }
            BinOp::Or | BinOp::And => {
                self.check_expr(env, e1, Sort::Bool)?;
                self.check_expr(env, e2, Sort::Bool)?;
                Ok(Sort::Bool)
            }
        }
    }

    fn emit_err<'a, T>(&'a self, err: impl SessionDiagnostic<'a>) -> Result<T, ErrorReported> {
        self.sess.emit_err(err);
        Err(ErrorReported)
    }
}

type Env = FxHashMap<Var, Sort>;

mod errors {
    use crate::ty;
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

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
