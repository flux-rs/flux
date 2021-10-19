use hashconsing::HConsed;
pub use rustc_middle::ty::{IntTy, UintTy};

pub mod context;
pub mod pure;
// mod subst;

pub use pure::{BinOp, Constant, Expr, ExprKind, RType, Refine, Sort, Var};

pub type Ty = HConsed<TyS>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TyS {
    kind: TyKind,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TyKind {
    Int(pure::Expr, IntTy),
    Uint(pure::Expr, UintTy),
}

#[derive(Debug)]
pub struct FnSig {
    pub params: Vec<(pure::Var, pure::RType)>,
    pub args: Vec<Ty>,
    pub ret: Ty,
}

impl TyS {
    pub fn kind(&self) -> &TyKind {
        &self.kind
    }
}
