use crate::{
    literal::{IntSize, Sign},
    BaseTy,
};

use std::fmt;

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Add(Sign, IntSize),
    Sub(Sign, IntSize),
    Mul(Sign, IntSize),
    Div(Sign, IntSize),
    Rem(Sign, IntSize),
    And,
    Or,
    Eq(BaseTy),
    Neq(BaseTy),
    Lt(Sign, IntSize),
    Gt(Sign, IntSize),
    Lte(Sign, IntSize),
    Gte(Sign, IntSize),
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Add { .. } => "+",
            Self::Sub { .. } => "-",
            Self::Mul { .. } => "*",
            Self::Div { .. } => "/",
            Self::Rem { .. } => "%",
            Self::And { .. } => "&&",
            Self::Or { .. } => "||",
            Self::Eq { .. } => "==",
            Self::Neq { .. } => "!=",
            Self::Lt { .. } => "<",
            Self::Gt { .. } => ">",
            Self::Lte { .. } => "<=",
            Self::Gte { .. } => ">=",
        };

        s.fmt(f)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum UnOp {
    Not,
    IntNot(Sign, IntSize),
    Neg(Sign, IntSize),
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::IntNot { .. } | Self::Not { .. } => "!",
            Self::Neg { .. } => "-",
        };

        s.fmt(f)
    }
}
