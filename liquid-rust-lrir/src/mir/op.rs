use crate::ty::BaseTy;

use std::fmt;

/// A primitive binary operator.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    /// The integer addition operator.
    Add,
    /// The integer substraction operator.
    Sub,
    /// The integer multiplication operator.
    Mul,
    /// The integer division operator.
    Div,
    /// The integer remainder operator.
    Rem,
    /// The equality operator for a particular base type.
    Eq(BaseTy),
    /// The "not equal to" operator for a particular base type.
    Neq(BaseTy),
    /// The "less than" integer operator.
    Lt,
    /// The "greater than" integer operator.
    Gt,
    /// The "less than or equal" integer operator.
    Lte,
    /// The "greater than or equal" integer operator.
    Gte,
    /// The boolean "and" operator.
    And,
    /// The boolean "or" operator.
    Or,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
            Self::And => "&&",
            Self::Or => "||",
            Self::Eq { .. } => "==",
            Self::Neq { .. } => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Lte => "<=",
            Self::Gte => ">=",
        };
        s.fmt(f)
    }
}

/// A primitive unary operator.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    /// The boolean negation operator.
    Not,
    /// The integer negation operator.
    Neg,
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Not => "!",
            Self::Neg => "-",
        };
        s.fmt(f)
    }
}
