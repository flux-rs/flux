use liquid_rust_common::{errors::ErrorReported, iter::IterExt};
use liquid_rust_core::ty;
use liquid_rust_syntax::ast;
use rustc_session::Session;
use rustc_span::{sym, Span, Symbol};

pub struct Resolver<'a> {
    sess: &'a Session,
    symbols: Symbols,
}

struct Symbols {
    int: Symbol,
}

impl Resolver<'_> {
    pub fn new(sess: &Session) -> Resolver {
        Resolver {
            sess,
            symbols: Symbols::new(),
        }
    }

    pub fn resolve_fn_sig(&self, fn_sig: ast::FnSig) -> Result<ty::FnSig, ErrorReported> {
        let params = fn_sig
            .params
            .into_iter()
            .map(|(ident, rty)| Ok((ident, self.resolve_rtype(rty)?)))
            .try_collect_exhaust();

        let args = fn_sig
            .args
            .into_iter()
            .map(|ty| self.resolve_ty(ty))
            .try_collect_exhaust();

        let ret = self.resolve_ty(fn_sig.ret);

        Ok(ty::FnSig {
            params: params?,
            args: args?,
            ret: ret?,
        })
    }

    pub fn resolve_ty(&self, ty: ast::Ty) -> Result<ty::Ty, ErrorReported> {
        match ty.name.symbol {
            sym::i32 => Ok(ty::Ty::Int(self.resolve_expr(ty.refine)?, ty::IntTy::I32)),
            _ => {
                self.emit_error(
                    &format!("unsupported type `{}`", ty.name.symbol),
                    ty.name.span,
                );
                Err(ErrorReported)
            }
        }
    }

    pub fn resolve_rtype(&self, rty: ast::RType) -> Result<ty::RType, ErrorReported> {
        let sort = self.resolve_sort(rty.sort);
        let pred = self.resolve_expr(rty.pred);

        Ok(ty::RType {
            sort: sort?,
            pred: pred?,
        })
    }

    pub fn resolve_expr(&self, expr: ast::Expr) -> Result<ty::Expr, ErrorReported> {
        let kind = match expr.kind {
            ast::ExprKind::Var(ident) => ty::ExprKind::Var(ident),
            ast::ExprKind::Literal(lit) => ty::ExprKind::Literal(self.resolve_lit(lit)?),
            ast::ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.resolve_expr(*e1);
                let e2 = self.resolve_expr(*e2);
                ty::ExprKind::BinaryOp(op, Box::new(e1?), Box::new(e2?))
            }
        };
        Ok(ty::Expr {
            kind,
            span: expr.span,
        })
    }

    fn resolve_lit(&self, lit: ast::Lit) -> Result<ty::Lit, ErrorReported> {
        let kind = match lit.kind {
            ast::LitKind::Integer => match lit.symbol.as_str().parse::<i128>() {
                Ok(n) => ty::LitKind::Int(n),
                Err(_) => {
                    self.emit_error("integer literal is too large", lit.span);
                    return Err(ErrorReported);
                }
            },
            _ => {
                self.sess.span_err(lit.span, "unexpected literal");
                return Err(ErrorReported);
            }
        };
        Ok(ty::Lit {
            kind,
            span: lit.span,
        })
    }

    fn resolve_sort(&self, sort: ast::Ident) -> Result<ty::Sort, ErrorReported> {
        if sort.symbol == self.symbols.int {
            Ok(ty::Sort::Int)
        } else {
            self.emit_error(
                &format!("cannot find sort `{}` in this scope", sort.symbol),
                sort.span,
            );
            Err(ErrorReported)
        }
    }

    fn emit_error(&self, message: &str, span: Span) {
        self.sess.span_err(span, message)
    }
}

impl Symbols {
    fn new() -> Self {
        Self {
            int: Symbol::intern("int"),
        }
    }
}
