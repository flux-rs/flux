use itertools::Itertools;
use std::fmt::{self, Write};

use liquid_rust_common::{format::PadAdapter, index::newtype_index};

pub enum Constraint {
    Pred(Pred),
    Conj(Vec<Self>),
    Guard(Expr, Box<Self>),
    ForAll(Var, Sort, Pred, Box<Self>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sort {
    Int,
    Bool,
}

pub enum Pred {
    And(Vec<Self>),
    KVar(KVid, Vec<Expr>),
    Expr(Expr),
}

pub enum Expr {
    Var(Var),
    Constant(Constant),
    BinaryOp(BinOp, Box<Self>, Box<Self>),
    UnaryOp(UnOp, Box<Self>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Eq,
    Add,
    Sub,
    Gt,
    Ge,
    Lt,
    Le,
    Or,
    And,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
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
        DEBUG_FORMAT = "v{}",
    }
}

impl Constraint {
    pub const TRUE: Self = Self::Pred(Pred::Expr(Expr::Constant(Constant::Bool(true))));
}

impl BinOp {
    pub fn precedence(&self) -> u32 {
        match self {
            BinOp::Add | BinOp::Sub => 4,
            BinOp::Eq | BinOp::Gt | BinOp::Lt | BinOp::Ge | BinOp::Le => 3,
            BinOp::And => 2,
            BinOp::Or => 1,
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
                write!(f, "(forall ((_ int) ({}))", body)?;
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
            Sort::Bool => write!(f, "bool"),
        }
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
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
            Expr::UnaryOp(op, e) => {
                if matches!(e.as_ref(), Expr::Constant(_) | Expr::Var(_)) {
                    write!(f, "{}{}", op, e)
                } else {
                    write!(f, "{}({})", op, e)
                }
            }
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Eq => write!(f, "="),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Gt => write!(f, ">"),
            BinOp::Ge => write!(f, ">="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Or => write!(f, "||"),
            BinOp::And => write!(f, "&&"),
        }
    }
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnOp::Not => write!(f, "~"),
            UnOp::Neg => write!(f, "-"),
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

impl From<bool> for Constant {
    fn from(b: bool) -> Self {
        Constant::Bool(b)
    }
}
