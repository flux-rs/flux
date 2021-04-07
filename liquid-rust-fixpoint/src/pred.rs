use crate::{
    constant::Constant,
    emit,
    emit::{Ctx, Emit},
};

use liquid_rust_lrir::{
    mir::{BinOp, UnOp},
    ty::KVid,
};
use std::fmt;

pub enum Pred {
    And(Vec<Self>),
    KVar(KVid, Vec<usize>),
    Expr(Expr),
}

pub enum Expr {
    Variable(usize),
    Constant(Constant),
    BinaryOp(BinOp, Box<Self>, Box<Self>),
    UnaryOp(UnOp, Box<Self>),
}

impl Emit for Pred {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        match self {
            Self::KVar(kvid, args) => {
                let vars = args
                    .iter()
                    .map(|v| format!("v{}", v))
                    .collect::<Vec<_>>()
                    .join(" ");

                write!(w, "({} {})", kvid, vars)
            }
            Self::And(preds) => {
                emit!(w, ctx, "(and")?;
                for pred in preds {
                    emit!(w, ctx, " {}", pred)?;
                }
                emit!(w, ctx, ")")
            }
            Self::Expr(expr) => emit!(w, ctx, "({})", expr),
        }
    }
}

impl Emit for Expr {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        fn should_parenthesize(bin_op: BinOp, child: &Expr) -> bool {
            if let Expr::BinaryOp(child_op, ..) = child {
                child_op.precedence() < bin_op.precedence()
                    || (child_op.precedence() == bin_op.precedence()
                        && !BinOp::associative(bin_op.precedence()))
            } else {
                false
            }
        }
        match self {
            Self::Variable(index) => write!(w, "v{}", index),
            Self::Constant(constant) => write!(w, "{}", constant),
            Self::BinaryOp(bin_op, op1, op2) => {
                if should_parenthesize(*bin_op, op1) {
                    emit!(w, ctx, "({})", op1)?;
                } else {
                    emit!(w, ctx, "{}", op1)?;
                }
                emit!(w, ctx, " {} ", bin_op)?;
                if should_parenthesize(*bin_op, op2) {
                    emit!(w, ctx, "({})", op2)?;
                } else {
                    emit!(w, ctx, "{}", op2)?;
                }
                Ok(())
            }
            Self::UnaryOp(un_op, op) => {
                if matches!(op.as_ref(), Expr::Variable(..) | Expr::Constant(..)) {
                    emit!(w, ctx, "{}{}", un_op, op)
                } else {
                    emit!(w, ctx, "{}({})", un_op, op)
                }
            }
        }
    }
}

impl Emit for UnOp {
    fn emit<W: fmt::Write>(&self, w: &mut W, _ctx: &Ctx) -> fmt::Result {
        match self {
            UnOp::Not => write!(w, "~"),
            UnOp::Neg => write!(w, "-"),
        }
    }
}

impl Emit for BinOp {
    fn emit<W: fmt::Write>(&self, w: &mut W, _ctx: &Ctx) -> fmt::Result {
        match self {
            BinOp::Eq(_) => write!(w, "="),
            _ => write!(w, "{}", self),
        }
    }
}
