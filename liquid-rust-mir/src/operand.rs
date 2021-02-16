use crate::{local::Local, ty::Literal};

use std::fmt;

#[derive(Clone)]
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
