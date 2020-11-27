use crate::{
    literal::{IntSize, Sign},
    ty::Ty,
};

use std::fmt;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BaseTy {
    Unit,
    Bool,
    Int(Sign, IntSize),
}

impl BaseTy {
    pub fn refined<A>(self) -> Ty<A> {
        Ty::Refined(self, true.into())
    }
}

impl fmt::Display for BaseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => "()".fmt(f),
            Self::Bool => "bool".fmt(f),
            Self::Int(sign, size) => write!(f, "{}{}", sign, size),
        }
    }
}
