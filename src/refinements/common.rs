pub use rustc_ast::ast::{IntTy, UintTy};
use rustc_middle::ty::{Ty, TyKind};

#[derive(Debug)]
pub enum BaseTy {
    Uint(UintTy),
    Int(IntTy),
    Bool,
}

impl<'tcx> BaseTy {
    pub fn unify(&self, rust_ty: Ty<'tcx>) {
        match (self, rust_ty.kind()) {
            (Self::Uint(ty1), TyKind::Uint(ty2)) if ty1 == ty2 => (),
            (Self::Int(ty1), TyKind::Int(ty2)) if ty1 == ty2 => (),
            (Self::Bool, TyKind::Bool) => (),
            _ => panic!(),
        }
    }
}

#[derive(Debug)]
pub enum Literal {
    Bool(bool),
    Int(i128),
}

#[derive(Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Eq,
    Neq,
    Lt,
    Gt,
    Lte,
    Gte,
}

#[derive(Debug)]
pub enum UnOp {
    Not,
    Neg,
}
