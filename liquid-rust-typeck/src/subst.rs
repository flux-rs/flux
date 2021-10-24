use rustc_hash::FxHashMap;

use crate::ty::{Expr, ExprKind, Ty, TyKind, Var};

pub struct Subst {
    map: FxHashMap<Var, Expr>,
}

impl Subst {
    pub fn new(map: impl IntoIterator<Item = (Var, Expr)>) -> Subst {
        Subst {
            map: map.into_iter().collect(),
        }
    }

    pub fn subst_ty(&self, ty: Ty) -> Ty {
        match ty.kind() {
            TyKind::Refine(bty, e) => TyKind::Refine(*bty, self.subst_expr(e.clone())).intern(),
            TyKind::Exists(bty, evar, e) => {
                // We keep the invariant that there is no shadowing
                TyKind::Exists(*bty, *evar, self.subst_expr(e.clone())).intern()
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
                ExprKind::BinaryOp(*op, e1, e2).intern()
            }
        }
    }

    pub fn subst_var(&self, x: Var) -> Expr {
        self.map
            .get(&x)
            .cloned()
            .unwrap_or_else(|| ExprKind::Var(x).intern())
    }
}
