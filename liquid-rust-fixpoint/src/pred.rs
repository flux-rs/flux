use crate::{
    constant::Constant,
    emit,
    emit::{Ctx, Emit},
    impl_emit_by_display,
};

use liquid_rust_lrir::{
    mir::{BinOp, UnOp},
    ty::KVid,
};
use std::fmt;

pub enum Pred {
    Kvar(KVid, Vec<usize>),
    Variable(usize),
    Constant(Constant),
    BinaryOp(BinOp, Box<Self>, Box<Self>),
    UnaryOp(UnOp, Box<Self>),
}

impl Emit for Pred {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        match self {
            Self::Kvar(kvid, args) => {
                let vars = args
                    .iter()
                    .map(|v| format!("v{}", v))
                    .collect::<Vec<_>>()
                    .join(", ");

                write!(w, "({} {})", kvid, vars)
            }
            Self::Variable(index) => write!(w, "v{}", index),
            Self::Constant(constant) => write!(w, "{}", constant),
            Self::BinaryOp(bin_op, lop, rop) => emit!(w, ctx, "({} {} {})", lop, bin_op, rop),
            Self::UnaryOp(un_op, op) => emit!(w, ctx, "({} {})", un_op, op),
        }
    }
}

impl_emit_by_display!(UnOp);

impl Emit for BinOp {
    fn emit<W: fmt::Write>(&self, w: &mut W, _ctx: &Ctx) -> fmt::Result {
        match self {
            BinOp::Eq(_) => write!(w, "="),
            _ => write!(w, "{}", self),
        }
    }
}
