use itertools::Itertools;
use std::fmt::{self, Write};

use liquid_rust_common::{format::PadAdapter, index::newtype_index};

pub enum Constraint {
    Pred(Pred),
    Conj(Vec<Self>),
    Guard(Pred, Box<Self>),
    ForAll(Var, Sort, Pred, Box<Self>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    Int,
}

pub enum Pred {
    And(Vec<Self>),
    KVar(KVid, Vec<usize>),
    Expr(Expr),
}

pub enum Expr {
    Var(Var),
    Constant(Constant),
    BinaryOp(BinOp, Box<Self>, Box<Self>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Eq,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constant {
    Int(Sign, u128),
    Bool(bool),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    Positive,
    Negative,
}

newtype_index! {
    pub struct KVid {
        DEBUG_FORMAT = "$k{}",
    }
}

newtype_index! {
    pub struct Var {
        DEBUG_FORMAT = "x{}",
    }
}

impl Constraint {
    pub const TRUE: Self = Self::Pred(Pred::Expr(Expr::Constant(Constant::Bool(true))));
}

impl BinOp {
    pub fn precedence(&self) -> u32 {
        match self {
            BinOp::Eq => 3,
        }
    }

    pub fn associative(precedence: u32) -> bool {
        precedence != 3
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Pred(pred) => write!(f, "({})", pred),
            Constraint::Conj(preds) => {
                write!(f, "(and")?;
                let mut w = PadAdapter::wrap_fmt(f);
                for pred in preds {
                    write!(w, "\n{}", pred)?;
                }
                write!(f, "\n)")
            }
            Constraint::Guard(body, head) => {
                write!(f, "(forall ((_ int) {})", body)?;
                write!(PadAdapter::wrap_fmt(f), "\n{}", head)?;
                write!(f, "\n)")
            }
            Constraint::ForAll(x, sort, body, head) => {
                write!(f, "(forall (({:?} {}) {})", x, sort, body)?;
                write!(PadAdapter::wrap_fmt(f), "\n{}", head)?;
                write!(f, "\n)")
            }
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Int => write!(f, "int"),
        }
    }
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pred::And(preds) => {
                write!(f, "(and")?;
                let mut w = PadAdapter::wrap_fmt(f);
                for pred in preds {
                    write!(w, "\n{}", pred)?;
                }
                write!(f, "\n)")
            }
            Pred::KVar(kvid, vars) => {
                write!(f, "({:?} {})", kvid, vars.iter().format(" "))
            }
            Pred::Expr(expr) => write!(f, "({})", expr),
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn should_parenthesize(op: BinOp, child: &Expr) -> bool {
            if let Expr::BinaryOp(child_op, ..) = child {
                child_op.precedence() < op.precedence()
                    || (child_op.precedence() == op.precedence()
                        && !BinOp::associative(op.precedence()))
            } else {
                false
            }
        }

        match self {
            Expr::Var(x) => write!(f, "{:?}", x),
            Expr::Constant(c) => write!(f, "{}", c),
            Expr::BinaryOp(op, e1, e2) => {
                if should_parenthesize(*op, e1) {
                    write!(f, "({})", e1)?;
                } else {
                    write!(f, "{}", e1)?;
                }
                write!(f, " {} ", op)?;
                if should_parenthesize(*op, e2) {
                    write!(f, "({})", e2)?;
                } else {
                    write!(f, "{}", e2)?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Eq => write!(f, "="),
        }
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Int(Sign::Positive, n) => write!(f, "{}", n),
            Constant::Int(Sign::Negative, n) => write!(f, "-{}", n),
            Constant::Bool(b) => write!(f, "{}", b),
        }
    }
}

impl From<u128> for Constant {
    fn from(c: u128) -> Self {
        Constant::Int(Sign::Positive, c)
    }
}

impl From<i128> for Constant {
    fn from(c: i128) -> Self {
        if c < 0 {
            Constant::Int(Sign::Negative, -c as u128)
        } else {
            Constant::Int(Sign::Positive, c as u128)
        }
    }
}
