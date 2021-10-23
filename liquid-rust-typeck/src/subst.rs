use rustc_hash::FxHashMap;

use crate::ty::{context::LrCtxt, Expr, ExprKind, Ty, TyKind, Var};

pub struct Subst<'a> {
    lr: &'a LrCtxt,
    map: FxHashMap<Var, Expr>,
}

impl Subst<'_> {
    pub fn new(lr: &LrCtxt, map: impl IntoIterator<Item = (Var, Expr)>) -> Subst {
        Subst {
            lr,
            map: map.into_iter().collect(),
        }
    }

    pub fn subst_ty(&self, ty: Ty) -> Ty {
        let lr = self.lr;
        match ty.kind() {
            TyKind::Refine(bty, e) => lr.mk_refine(*bty, self.subst_expr(e.clone())),
            TyKind::Exists(bty, evar, e) => {
                // We keep the invariant that there is no shadowing
                lr.mk_exists(*bty, *evar, self.subst_expr(e.clone()))
            }
            TyKind::Uninit(_) | TyKind::MutRef(_) => ty,
        }
    }

    pub fn subst_expr(&self, e: Expr) -> Expr {
        match e.kind() {
            ExprKind::Var(x) => self.subst_var(*x),
            ExprKind::Constant(_) => e,
            ExprKind::BinaryOp(op, e1, e2) => {
                let e1 = self.subst_expr(e1.clone());
                let e2 = self.subst_expr(e2.clone());
                self.lr.mk_bin_op(*op, e1, e2)
            }
        }
    }

    pub fn subst_var(&self, x: Var) -> Expr {
        self.map
            .get(&x)
            .cloned()
            .unwrap_or_else(|| self.lr.mk_var(x))
    }
}
