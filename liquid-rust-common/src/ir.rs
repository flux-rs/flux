use crate::ty::IntSize;

use std::fmt::{Display, Formatter, Result};

#[derive(Debug, Copy, Clone)]
pub enum Literal {
    Unit,
    Bool(bool),
    Uint(u128, IntSize),
    Int(i128, IntSize),
}

impl From<bool> for Literal {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<()> for Literal {
    fn from((): ()) -> Self {
        Self::Unit
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Unit => "()".fmt(f),
            Self::Bool(b) => b.fmt(f),
            Self::Uint(uint, _) => uint.fmt(f),
            Self::Int(int, _) => int.fmt(f),
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
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

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let s = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::And => "&&",
            Self::Or => "||",
            Self::Eq => "==",
            Self::Neq => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Lte => "<=",
            Self::Gte => ">=",
        };

        s.fmt(f)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnOp {
    Not,
    Neg,
}

impl Display for UnOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let s = match self {
            Self::Not => "!",
            Self::Neg => "-",
        };

        s.fmt(f)
    }
}
