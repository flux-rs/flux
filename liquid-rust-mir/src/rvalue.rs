use crate::operand::Operand;

use liquid_rust_ty::{BinOp, UnOp};

use std::fmt;

pub enum Rvalue {
    Use(Operand),
    UnApp(UnOp, Operand),
    BinApp(BinOp, Operand, Operand),
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Use(operand) => operand.fmt(f),
            Self::UnApp(un_op, op) => write!(f, "{}{}", un_op, op),
            Self::BinApp(bin_op, op1, op2) => write!(f, "{} {} {}", op1, bin_op, op2),
        }
    }
}
