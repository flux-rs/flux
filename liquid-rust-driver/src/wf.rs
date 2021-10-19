use liquid_rust_common::errors::ErrorReported;
use liquid_rust_core::ty as core;
use quickscope::ScopeSet;
use rustc_session::Session;
use rustc_span::{Span, Symbol};

pub struct Wf<'a> {
    sess: &'a Session,
    name_map: ScopeSet<Symbol>,
    error_reported: bool,
}

impl Wf<'_> {
    pub fn check(sess: &Session, fn_sig: &core::FnSig) -> Result<(), ErrorReported> {
        let mut wf = Wf {
            sess,
            name_map: ScopeSet::new(),
            error_reported: false,
        };
        wf.check_fn_sig(fn_sig);
        if wf.error_reported {
            Err(ErrorReported)
        } else {
            Ok(())
        }
    }

    fn check_fn_sig(&mut self, fn_sig: &core::FnSig) {
        fn_sig.params.iter().for_each(|(ident, rty)| {
            self.name_map.define(ident.symbol);
            self.check_rtype(rty);
        });

        fn_sig.args.iter().for_each(|ty| self.check_ty(ty));

        self.check_ty(&fn_sig.ret);
    }

    fn check_ty(&mut self, ty: &core::Ty) {
        match ty {
            core::Ty::Int(n, _int_ty) => self.check_expr(n),
        }
    }

    fn check_rtype(&mut self, rty: &core::RType) {
        self.check_expr(&rty.pred);
    }

    fn check_expr(&mut self, expr: &core::Expr) {
        match &expr.kind {
            core::ExprKind::Var(ident) => {
                if !self.name_map.contains(&ident.symbol) {
                    self.emit_error(
                        &format!("cannot find value `{}` in this scope", ident.symbol),
                        ident.span,
                    );
                }
            }
            core::ExprKind::Literal(..) => {}
            core::ExprKind::BinaryOp(_op, e1, e2) => {
                self.check_expr(e1);
                self.check_expr(e2);
            }
        }
    }

    fn emit_error(&mut self, message: &str, span: Span) {
        self.error_reported = true;
        self.sess.span_err(span, message)
    }
}
