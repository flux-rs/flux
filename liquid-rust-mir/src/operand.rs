use crate::local::Local;

use liquid_rust_ty::Literal;

use std::fmt;

pub enum Operand {
    Local(Local),
    Literal(Literal),
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Local(local) => local.fmt(f),
            Self::Literal(literal) => literal.fmt(f),
        }
    }
}
