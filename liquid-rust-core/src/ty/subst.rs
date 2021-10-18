use rustc_hash::FxHashMap;

use super::{
    context::LrCtxt,
    pure::{Expr, ExprKind, RType, Refine, Var},
    Ty, TyKind,
};

pub struct Subst<'a> {
    map: FxHashMap<Var, Expr>,
    lr: &'a LrCtxt,
}

impl<'a> Subst<'a> {
    pub fn new(lr: &'a LrCtxt) -> Self {
        Subst {
            map: FxHashMap::default(),
            lr,
        }
    }

    pub fn insert(&mut self, x: Var, expr: Expr) {
        self.map.insert(x, expr);
    }

    pub fn subst_ty(&self, ty: Ty) -> Ty {
        let kind = match ty.kind() {
            TyKind::Int(n, int_ty) => TyKind::Int(self.subst_expr(n.clone()), *int_ty),
            TyKind::Uint(n, int_ty) => TyKind::Uint(self.subst_expr(n.clone()), *int_ty),
        };
        self.lr.mk_ty(kind)
    }

    pub fn subst_rtype(&self, rty: RType) -> RType {
        RType {
            sort: rty.sort,
            refine: self.subst_refine(rty.refine),
        }
    }

    fn subst_refine(&self, refine: Refine) -> Refine {
        match refine {
            // Refine::KVar(kvid) => Refine::KVar(kvid),
            Refine::Pred(expr) => Refine::Pred(self.subst_expr(expr)),
        }
    }

    fn subst_expr(&self, expr: Expr) -> Expr {
        match expr.kind() {
            ExprKind::Var(x) => self.subst_var(*x),
            ExprKind::BinaryOp(op, e1, e2) => self.lr.mk_bin_op(
                *op,
                self.subst_expr(e1.clone()),
                self.subst_expr(e2.clone()),
            ),
            ExprKind::Constant(_) => expr,
        }
    }

    fn subst_var(&self, var: Var) -> Expr {
        self.map
            .get(&var)
            .cloned()
            .unwrap_or_else(|| self.lr.mk_var(var))
    }
}
