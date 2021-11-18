use liquid_rust_common::{errors::ErrorReported, index::IndexGen, iter::IterExt};
use liquid_rust_core::ty::{self, Name, ParamTy};
use liquid_rust_syntax::ast;
use quickscope::ScopeMap;
use rustc_hash::FxHashMap;
use rustc_session::Session;
use rustc_span::{sym, symbol::kw, Span, Symbol};

pub struct Resolver<'a> {
    sess: &'a Session,
    symbols: Symbols,
}

struct Symbols {
    int: Symbol,
}

struct Subst {
    exprs: ScopeMap<Symbol, ty::Var>,
    regions: FxHashMap<Symbol, Name>,
    types: FxHashMap<Symbol, ParamTy>,
}

impl<'a> Resolver<'a> {
    pub fn new(sess: &'a Session) -> Self {
        Self {
            sess,
            symbols: Symbols::new(),
        }
    }

    pub fn resolve(&self, fn_sig: ast::FnSig) -> Result<ty::FnSig, ErrorReported> {
        let mut subst = Subst::new();
        let name_gen = IndexGen::new();

        let params = self.resolve_params(fn_sig.params, &name_gen, &mut subst);

        let requires = fn_sig
            .requires
            .into_iter()
            .map(|(ident, ty)| {
                let name = name_gen.fresh();
                if subst.insert_region(ident.symbol, name).is_some() {
                    self.sess.span_err(ident.span, "duplicate region");
                    return Err(ErrorReported);
                };
                let ident = ty::Ident {
                    name,
                    symbol: ident.symbol,
                    span: ident.span,
                };
                let ty = self.resolve_ty(ty, &mut subst);
                Ok((ident, ty?))
            })
            .try_collect_exhaust();

        let args = fn_sig
            .args
            .into_iter()
            .map(|ty| self.resolve_ty(ty, &mut subst))
            .try_collect_exhaust();

        let ret = self.resolve_ty(fn_sig.ret, &mut subst);

        let ensures = fn_sig
            .ensures
            .into_iter()
            .map(|(ident, ty)| {
                let ident = self.resolve_region_ident(ident, &subst);
                let ty = self.resolve_ty(ty, &mut subst);
                Ok((ident?, ty?))
            })
            .try_collect_exhaust();

        Ok(ty::FnSig {
            params: params?,
            requires: requires?,
            args: args?,
            ret: ret?,
            ensures: ensures?,
        })
    }

    fn resolve_params(
        &self,
        params: Vec<ast::Param>,
        name_gen: &IndexGen<Name>,
        subst: &mut Subst,
    ) -> Result<Vec<ty::Param>, ErrorReported> {
        let mut pure_params = vec![];
        let mut has_errors = false;
        let mut next_param_ty_idx = 0;
        for param in params {
            match param {
                ast::Param::Pure { name, sort, pred } => {
                    if let Ok(param) = self.resolve_pure_param(name, sort, pred, subst, name_gen) {
                        pure_params.push(param)
                    } else {
                        has_errors = true;
                    }
                }
                ast::Param::Type(param) => {
                    let param_ty = ParamTy {
                        index: next_param_ty_idx,
                        name: param.symbol,
                    };
                    if subst.insert_type(param.symbol, param_ty).is_some() {
                        self.sess.span_err(param.span, "duplicate parameter name");
                        has_errors = true;
                    }
                    next_param_ty_idx += 1;
                }
            }
        }
        if has_errors {
            Err(ErrorReported)
        } else {
            Ok(pure_params)
        }
    }

    fn resolve_pure_param(
        &self,
        name: ast::Ident,
        sort: ast::Ident,
        pred: Option<ast::Expr>,
        subst: &mut Subst,
        name_gen: &IndexGen<Name>,
    ) -> Result<ty::Param, ErrorReported> {
        let fresh = name_gen.fresh();
        if subst
            .insert_expr(name.symbol, ty::Var::Free(fresh))
            .is_some()
        {
            self.sess.span_err(name.span, "duplicate parameter name");
            Err(ErrorReported)
        } else {
            let name = ty::Ident {
                name: fresh,
                symbol: name.symbol,
                span: name.span,
            };
            let sort = self.resolve_sort(sort);
            let pred = match pred {
                Some(expr) => self.resolve_expr(expr, &subst),
                None => Ok(ty::Expr::TRUE),
            };
            Ok(ty::Param {
                name,
                sort: sort?,
                pred: pred?,
            })
        }
    }

    fn resolve_ty(&self, ty: ast::Ty, subst: &mut Subst) -> Result<ty::Ty, ErrorReported> {
        match ty.kind {
            ast::TyKind::RefineTy { bty, refine } => {
                let bty = self.resolve_bty(bty);
                let refine = self.resolve_expr(refine, subst);
                Ok(ty::Ty::Refine(bty?, refine?))
            }
            ast::TyKind::Exists { bind, bty, pred } => {
                let bty = self.resolve_bty(bty);
                subst.push_expr_layer();
                subst.insert_expr(bind.symbol, ty::Var::Bound);
                let e = self.resolve_expr(pred, subst);
                subst.pop_expr_layer();
                Ok(ty::Ty::Exists(bty?, ty::Pred::Expr(e?)))
            }
            ast::TyKind::BaseTy(bty) => {
                if let Some(param_ty) = subst.get_type(bty.symbol) {
                    Ok(ty::Ty::Param(param_ty))
                } else {
                    let bty = self.resolve_bty(bty)?;
                    Ok(ty::Ty::Exists(bty, ty::Pred::TRUE))
                }
            }
            ast::TyKind::MutRef(region) => {
                Ok(ty::Ty::MutRef(self.resolve_region_ident(region, subst)?))
            }
            ast::TyKind::Param(param) => Ok(ty::Ty::Param(self.resolve_type_param(param, subst)?)),
        }
    }

    fn resolve_type_param(
        &self,
        param: ast::Ident,
        subst: &Subst,
    ) -> Result<ParamTy, ErrorReported> {
        match subst.get_type(param.symbol) {
            Some(param_ty) => Ok(param_ty),
            None => {
                self.sess.span_err(param.span, "unknown type parameter");
                Err(ErrorReported)
            }
        }
    }

    fn resolve_bty(&self, ident: ast::Ident) -> Result<ty::BaseTy, ErrorReported> {
        match ident.symbol {
            sym::i32 => Ok(ty::BaseTy::Int(ty::IntTy::I32)),
            sym::bool => Ok(ty::BaseTy::Bool),
            _ => {
                self.emit_error(&format!("unsupported type: `{}`", ident.symbol), ident.span);
                Err(ErrorReported)
            }
        }
    }

    fn resolve_expr(&self, expr: ast::Expr, subst: &Subst) -> Result<ty::Expr, ErrorReported> {
        let kind = match expr.kind {
            ast::ExprKind::Var(ident) => {
                ty::ExprKind::Var(self.resolve_var(ident, subst)?, ident.symbol, ident.span)
            }
            ast::ExprKind::Literal(lit) => ty::ExprKind::Literal(self.resolve_lit(lit)?),
            ast::ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.resolve_expr(*e1, subst);
                let e2 = self.resolve_expr(*e2, subst);
                ty::ExprKind::BinaryOp(op, Box::new(e1?), Box::new(e2?))
            }
        };
        Ok(ty::Expr {
            kind,
            span: Some(expr.span),
        })
    }

    fn resolve_region_ident(
        &self,
        ident: ast::Ident,
        subst: &Subst,
    ) -> Result<ty::Ident, ErrorReported> {
        match subst.get_region(ident.symbol) {
            Some(name) => Ok(ty::Ident {
                span: ident.span,
                symbol: ident.symbol,
                name,
            }),
            None => {
                self.emit_error(
                    &format!("cannot region parameter `{}` in this scope", ident.symbol),
                    ident.span,
                );
                Err(ErrorReported)
            }
        }
    }

    fn resolve_var(&self, ident: ast::Ident, subst: &Subst) -> Result<ty::Var, ErrorReported> {
        match subst.get_expr(ident.symbol) {
            Some(var) => Ok(var),
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
        match lit.kind {
            ast::LitKind::Integer => match lit.symbol.as_str().parse::<i128>() {
                Ok(n) => Ok(ty::Lit::Int(n)),
                Err(_) => {
                    self.emit_error("integer literal is too large", lit.span);
                    Err(ErrorReported)
                }
            },
            ast::LitKind::Bool => Ok(ty::Lit::Bool(lit.symbol == kw::True)),
            _ => {
                self.sess.span_err(lit.span, "unexpected literal");
                Err(ErrorReported)
            }
        }
    }

    fn resolve_sort(&self, sort: ast::Ident) -> Result<ty::Sort, ErrorReported> {
        if sort.symbol == self.symbols.int {
            Ok(ty::Sort::Int)
        } else if sort.symbol == sym::bool {
            Ok(ty::Sort::Bool)
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

impl Subst {
    fn new() -> Self {
        Self {
            exprs: ScopeMap::new(),
            regions: FxHashMap::default(),
            types: FxHashMap::default(),
        }
    }

    fn push_expr_layer(&mut self) {
        self.exprs.push_layer();
    }

    fn pop_expr_layer(&mut self) {
        self.exprs.pop_layer();
    }

    fn insert_expr(&mut self, symb: Symbol, name: ty::Var) -> Option<ty::Var> {
        let old = if self.exprs.contains_key_at_top(&symb) {
            self.exprs.get(&symb).copied()
        } else {
            None
        };
        self.exprs.define(symb, name);
        old
    }

    fn insert_region(&mut self, symb: Symbol, name: Name) -> Option<Name> {
        self.regions.insert(symb, name)
    }

    fn insert_type(&mut self, symb: Symbol, param_ty: ParamTy) -> Option<ParamTy> {
        self.types.insert(symb, param_ty)
    }

    fn get_expr(&self, symb: Symbol) -> Option<ty::Var> {
        self.exprs.get(&symb).copied()
    }

    fn get_region(&self, symb: Symbol) -> Option<Name> {
        self.regions.get(&symb).copied()
    }

    fn get_type(&self, symb: Symbol) -> Option<ParamTy> {
        self.types.get(&symb).copied()
    }
}
