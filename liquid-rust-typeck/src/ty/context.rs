use std::cell::RefCell;

use hashconsing::{HConsign, HashConsign};

use super::{
    BaseTy, BinOp, Constant, Expr, ExprKind, ExprS, Region, Ty, TyKind, TyS, TypeLayout, Var,
};

pub struct LrCtxt {
    interner: RefCell<Interner>,
    pub exprs: CommonExprs,
}

pub struct CommonExprs {
    tt: Expr,
}

struct Interner {
    types: HConsign<TyS>,
    exprs: HConsign<ExprS>,
}

impl LrCtxt {
    pub fn new() -> Self {
        let mut interner = Interner::new();
        let exprs = CommonExprs::new(&mut interner);
        LrCtxt {
            interner: RefCell::new(interner),
            exprs,
        }
    }

    // Types

    pub fn mk_ty(&self, kind: TyKind) -> Ty {
        self.interner.borrow_mut().intern_ty(kind)
    }

    pub fn mk_refine(&self, bty: BaseTy, e: Expr) -> Ty {
        self.mk_ty(TyKind::Refine(bty, e))
    }

    pub fn mk_exists(&self, bty: BaseTy, evar: Var, e: Expr) -> Ty {
        self.mk_ty(TyKind::Exists(bty, evar, e))
    }

    pub fn mk_uninit(&self, layout: TypeLayout) -> Ty {
        self.mk_ty(TyKind::Uninit(layout))
    }

    pub fn mk_mut_ref(&self, r: impl Into<Region>) -> Ty {
        self.mk_ty(TyKind::MutRef(r.into()))
    }

    pub fn uninit(&self, ty: Ty) -> Ty {
        self.mk_ty(TyKind::Uninit(ty.layout()))
    }

    // Exprs

    pub fn mk_expr(&self, kind: ExprKind) -> Expr {
        self.interner.borrow_mut().intern_expr(kind)
    }

    pub fn mk_var(&self, x: Var) -> Expr {
        self.mk_expr(ExprKind::Var(x))
    }

    pub fn mk_constant(&self, c: Constant) -> Expr {
        self.mk_expr(ExprKind::Constant(c))
    }

    pub fn mk_bin_op(&self, bin_op: BinOp, e1: Expr, e2: Expr) -> Expr {
        self.mk_expr(ExprKind::BinaryOp(bin_op, e1, e2))
    }
}

impl Interner {
    fn new() -> Self {
        Interner {
            types: HConsign::empty(),
            exprs: HConsign::empty(),
        }
    }

    fn intern_ty(&mut self, kind: TyKind) -> Ty {
        self.types.mk(TyS { kind })
    }

    fn intern_expr(&mut self, kind: ExprKind) -> Expr {
        self.exprs.mk(ExprS { kind })
    }
}

impl CommonExprs {
    fn new(interner: &mut Interner) -> Self {
        let mut intern = |kind| interner.intern_expr(kind);
        Self {
            tt: intern(ExprKind::Constant(Constant::Bool(true))),
        }
    }

    pub fn tt(&self) -> Expr {
        self.tt.clone()
    }
}
