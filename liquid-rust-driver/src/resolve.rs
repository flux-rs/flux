use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
use liquid_rust_core::ty::{self, Name};
use liquid_rust_syntax::ast;
use quickscope::ScopeMap;
use rustc_session::Session;
use rustc_span::{sym, Span, Symbol};

pub struct Resolver<'a> {
    sess: &'a Session,
    symbols: Symbols,
}

struct Symbols {
    int: Symbol,
}

type Map = ScopeMap<Symbol, Name>;

impl Resolver<'_> {
    pub fn new(sess: &Session) -> Resolver {
        Resolver {
            sess,
            symbols: Symbols::new(),
        }
    }

    pub fn resolve_fn_sig(&self, fn_sig: ast::FnSig) -> Result<ty::FnSig, ErrorReported> {
        let name_gen = IndexGen::new();
        let mut map = ScopeMap::new();

        let params = fn_sig
            .params
            .into_iter()
            .map(|param| {
                let name = name_gen.fresh();
                map.push_layer();
                map.define(param.name.symbol, name);
                let name = ty::Ident {
                    name,
                    span: param.name.span,
                };
                let sort = self.resolve_sort(param.sort);
                let pred = self.resolve_expr(param.pred, &map);
                Ok(ty::Param {
                    name,
                    sort: sort?,
                    pred: pred?,
                })
            })
            .try_collect_exhaust();

        let args = fn_sig
            .args
            .into_iter()
            .map(|ty| self.resolve_ty(ty, &map))
            .try_collect_exhaust();

        let ret = self.resolve_ty(fn_sig.ret, &map);

        Ok(ty::FnSig {
            params: params?,
            args: args?,
            ret: ret?,
        })
    }

    pub fn resolve_ty(&self, ty: ast::Ty, map: &Map) -> Result<ty::Ty, ErrorReported> {
        match ty.name.symbol {
            sym::i32 => Ok(ty::Ty::Int(
                self.resolve_refine(ty.refine, map)?,
                ty::IntTy::I32,
            )),
            _ => {
                self.emit_error(
                    &format!("unsupported type `{}`", ty.name.symbol),
                    ty.name.span,
                );
                Err(ErrorReported)
            }
        }
    }

    pub fn resolve_refine(
        &self,
        refine: ast::Refine,
        map: &Map,
    ) -> Result<ty::Refine, ErrorReported> {
        match refine {
            ast::Refine::Var(ident) => Ok(ty::Refine::Var(self.resolve_ident(ident, map)?)),
            ast::Refine::Literal(lit) => Ok(ty::Refine::Literal(self.resolve_lit(lit)?)),
        }
    }

    pub fn resolve_expr(&self, expr: ast::Expr, map: &Map) -> Result<ty::Expr, ErrorReported> {
        let kind = match expr.kind {
            ast::ExprKind::Var(ident) => ty::ExprKind::Var(self.resolve_ident(ident, map)?),
            ast::ExprKind::Literal(lit) => ty::ExprKind::Literal(self.resolve_lit(lit)?),
            ast::ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.resolve_expr(*e1, map);
                let e2 = self.resolve_expr(*e2, map);
                ty::ExprKind::BinaryOp(op, Box::new(e1?), Box::new(e2?))
            }
        };
        Ok(ty::Expr {
            kind,
            span: expr.span,
        })
    }

    pub fn resolve_ident(&self, ident: ast::Ident, map: &Map) -> Result<ty::Ident, ErrorReported> {
        match map.get(&ident.symbol) {
            Some(name) => Ok(ty::Ident {
                span: ident.span,
                name: *name,
            }),
            None => {
                self.emit_error(
                    &format!("cannot find value `{}` in this scope", ident.symbol),
                    ident.span,
                );
                Err(ErrorReported)
            }
        }
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
