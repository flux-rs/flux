use crate::mir::{BinOp, Operand, Place, UnOp};
use crate::ty::{BorrowKind, Region};

pub enum Rvalue {
    Use(Operand),
    Ref(Region, BorrowKind, Place),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
}
