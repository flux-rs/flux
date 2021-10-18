use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
use liquid_rust_core::ty::{self, context::LrCtxt};
use liquid_rust_parser::ast;
use quickscope::ScopeMap;
use rustc_session::Session;
use rustc_span::{sym, Span, Symbol};

pub struct Wf<'wf> {
    lr: &'wf LrCtxt,
    sess: &'wf Session,
    name_map: ScopeMap<Symbol, ty::Var>,
    name_gen: IndexGen<ty::Var>,
    symbols: Symbols,
}

struct Symbols {
    int: Symbol,
}

impl Wf<'_> {
    pub fn check(
        lr: &LrCtxt,
        sess: &Session,
        fn_sig: ast::FnSig,
    ) -> Result<ty::FnSig, ErrorReported> {
        let mut wf = Wf {
            lr,
            sess,
            name_map: ScopeMap::new(),
            name_gen: IndexGen::new(),
            symbols: Symbols::new(),
        };
        wf.check_fn_sig(fn_sig)
    }

    fn check_fn_sig(&mut self, fn_sig: ast::FnSig) -> Result<ty::FnSig, ErrorReported> {
        let params = fn_sig
            .params
            .into_iter()
            .map(|(ident, rty)| {
                let fresh = self.name_gen.fresh();
                self.name_map.push_layer();
                self.name_map.define(ident.symbol, fresh);
                Ok((fresh, self.check_rtype(rty)?))
            })
            .try_collect_exhaust();

        let args = fn_sig
            .args
            .into_iter()
            .map(|ty| self.check_ty(ty))
            .try_collect_exhaust();

        let ret = self.check_ty(fn_sig.ret);

        Ok(ty::FnSig {
            params: params?,
            args: args?,
            ret: ret?,
        })
    }

    fn check_ty(&mut self, ty: ast::Ty) -> Result<ty::Ty, ErrorReported> {
        if ty.name.symbol == sym::i32 {
            Ok(self.lr.mk_int(self.check_expr(ty.refine)?, ty::IntTy::I32))
        } else {
            self.emit_error(
                &format!("Cannot find type `{}` in this scope", ty.name.symbol),
                ty.name.span,
            );
            Err(ErrorReported)
        }
    }

    fn check_rtype(&mut self, rty: ast::RType) -> Result<ty::RType, ErrorReported> {
        let sort = self.resolve_sort(rty.sort);
        let pred = self.check_expr(rty.pred);

        Ok(ty::RType {
            sort: sort?,
            refine: ty::Refine::Pred(pred?),
        })
    }

    fn check_expr(&mut self, expr: ast::Expr) -> Result<ty::Expr, ErrorReported> {
        let lr = self.lr;
        match expr.kind {
            ast::ExprKind::Var(ident) => match self.name_map.get(&ident.symbol) {
                Some(x) => Ok(lr.mk_var(*x)),
                None => {
                    self.emit_error(
                        &format!("cannot find value `{}` in this scope", ident.symbol),
                        ident.span,
                    );
                    Err(ErrorReported)
                }
            },
            ast::ExprKind::Literal(ast::Lit {
                kind: ast::LitKind::Int(n),
                ..
            }) => Ok(lr.mk_constant(ty::Constant::from(n))),
            ast::ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.check_expr(*e1);
                let e2 = self.check_expr(*e2);
                Ok(lr.mk_bin_op(map_bin_op(op), e1?, e2?))
            }
        }
    }

    fn resolve_sort(&mut self, sort: ast::Ident) -> Result<ty::Sort, ErrorReported> {
        if sort.symbol == self.symbols.int {
            Ok(ty::Sort::Int)
        } else {
            self.emit_error(
                &format!("Cannot find base type `{}` in this scope", sort.symbol),
                sort.span,
            );
            Err(ErrorReported)
        }
    }

    fn emit_error(&mut self, message: &str, span: Span) {
        self.sess.span_err(span, message)
    }
}

fn map_bin_op(op: ast::BinaryOp) -> ty::BinOp {
    match op {
        ast::BinaryOp::Eq => ty::BinOp::Eq,
    }
}

impl Symbols {
    fn new() -> Self {
        Self {
            int: Symbol::intern("int"),
        }
    }
}
