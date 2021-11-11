use liquid_rust_common::{errors::ErrorReported, iter::IterExt};
use rustc_hash::FxHashMap;
use rustc_session::Session;
use rustc_span::{MultiSpan, Span};

use crate::ty::{BinOp, Expr, ExprKind, FnSig, Name, Sort, Ty};

pub struct Wf<'a> {
    sess: &'a Session,
}

impl Wf<'_> {
    pub fn new(sess: &Session) -> Wf {
        Wf { sess }
    }

    pub fn check_fn_sig(&self, fn_sig: &FnSig) -> Result<(), ErrorReported> {
        let mut env = Env::default();
        for param in &fn_sig.params {
            env.insert(param.name.name, param.sort);
        }

        let args = fn_sig
            .args
            .iter()
            .map(|ty| self.check_type(&mut env, ty))
            .try_collect_exhaust();

        let ret = self.check_type(&mut env, &fn_sig.ret);

        args?;
        ret?;

        Ok(())
    }

    fn check_type(&self, env: &mut Env, ty: &Ty) -> Result<(), ErrorReported> {
        match ty {
            Ty::Refine(bty, e) => self.check_expr(env, e, bty.sort()),
            Ty::Exists(bty, var, e) => {
                // We are assuming no variable shadowing which is guaranteed by the resolve phase.
                debug_assert!(!env.contains_key(var));

                env.insert(*var, bty.sort());
                let result = self.check_expr(env, e, Sort::Bool);
                env.remove(var);
                result
            }
        }
    }

    fn check_expr(&self, env: &Env, e: &Expr, expected: Sort) -> Result<(), ErrorReported> {
        let s = self.synth_expr(env, e)?;
        if s != expected {
            self.report_mismatch(expected, s, e.span)
        } else {
            Ok(())
        }
    }

    fn synth_expr(&self, env: &Env, e: &Expr) -> Result<Sort, ErrorReported> {
        match &e.kind {
            ExprKind::Var(ident) => Ok(env[&ident.name]),
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
            BinOp::Eq => {
                let s = self.synth_expr(env, e1)?;
                self.check_expr(env, e2, s)?;
                Ok(Sort::Bool)
            }
            BinOp::Add => {
                self.check_expr(env, e1, Sort::Int)?;
                self.check_expr(env, e2, Sort::Int)?;
                Ok(Sort::Int)
            }
            BinOp::Or | BinOp::And => {
                self.check_expr(env, e1, Sort::Bool)?;
                self.check_expr(env, e2, Sort::Bool)?;
                Ok(Sort::Bool)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.check_expr(env, e1, Sort::Int)?;
                self.check_expr(env, e2, Sort::Int)?;
                Ok(Sort::Bool)
            }
        }
    }

    fn report_mismatch(
        &self,
        expected: Sort,
        found: Sort,
        span: Option<Span>,
    ) -> Result<(), ErrorReported> {
        if let Some(span) = span {
            let mut s = MultiSpan::from_span(span);
            s.push_span_label(span, format!("expected `{}`, found `{}`", expected, found));
            self.sess.span_err(s, "mismatched sorts");
        } else {
            self.sess.err(&format!(
                "mismatched sorts expected `{}`, found `{}`",
                expected, found
            ));
        }

        Err(ErrorReported)
    }
}

type Env = FxHashMap<Name, Sort>;
