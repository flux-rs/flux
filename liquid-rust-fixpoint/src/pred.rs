use crate::{
    constant::Constant, emit, emit::Emit, impl_emit_by_display, variable::Variable, Fixpoint,
};

use liquid_rust_lrir::mir::{BinOp, UnOp};

use std::fmt;

pub enum Pred {
    Constant(Constant),
    Variable(Variable),
    BinaryOp(BinOp, Box<Self>, Box<Self>),
    UnaryOp(UnOp, Box<Self>),
}

impl Emit for Pred {
    fn emit<W: fmt::Write>(&self, w: &mut W, fixpoint: &Fixpoint) -> fmt::Result {
        match self {
            Self::Constant(constant) => write!(w, "{}", constant),
            Self::Variable(variable) => write!(w, "{}", variable),
            Self::BinaryOp(bin_op, lop, rop) => emit!(w, fixpoint, "({} {} {})", bin_op, lop, rop),
            Self::UnaryOp(un_op, op) => emit!(w, fixpoint, "({} {})", un_op, op),
        }
    }
}

impl_emit_by_display!(BinOp);
impl_emit_by_display!(UnOp);
