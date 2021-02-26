use crate::mir::{Operand, Place};
use crate::ty::{BinOp, BorrowKind, Region, UnOp};

pub enum Rvalue {
    Use(Operand),
    Ref(Region, BorrowKind, Place),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
}
