use crate::{
    mir::{BinOp, Operand, Place, UnOp},
    ty::{BorrowKind, Region},
};

pub enum Rvalue {
    Use(Operand),
    Ref(Region, BorrowKind, Place),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
}
