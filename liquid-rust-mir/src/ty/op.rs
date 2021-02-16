use crate::ty::{base_ty::BaseTy, int_sign::IntSign, int_size::IntSize};

use std::fmt;

/// A primitive binary operator.
///
/// These operators are typed, meaning that they specify the type of their operands.
#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    /// The integer addition operator.
    Add(IntSign, IntSize),
    /// The integer substraction operator.
    Sub(IntSign, IntSize),
    /// The integer multiplication operator.
    Mul(IntSign, IntSize),
    /// The integer division operator.
    Div(IntSign, IntSize),
    /// The integer remainder operator.
    Rem(IntSign, IntSize),
    /// The logical and operator.
    And,
    /// The logical or operator.
    Or,
    /// The equality operator.Blanket Implementations
    Eq(BaseTy),
    /// The "not equal to" operator.
    Neq(BaseTy),
    /// The "less than" integer operator.
    Lt(IntSign, IntSize),
    /// The "greater than" integer operator.
    Gt(IntSign, IntSize),
    /// The "less than or equal" integer operator.
    Lte(IntSign, IntSize),
    /// The "greater than or equal" integer operator.
    Gte(IntSign, IntSize),
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

/// A primitive unary operator.
///
/// These operators are typed, meaning that they specify the type of their operands.
#[derive(Debug, Copy, Clone)]
pub enum UnOp {
    /// The logical negation operator.
    Not,
    /// The integer negation operator.
    Neg(IntSign, IntSize),
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Not { .. } => "!",
            Self::Neg { .. } => "-",
        };

        s.fmt(f)
    }
}
