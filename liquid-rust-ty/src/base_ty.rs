use crate::ty::Ty;

use liquid_rust_common::literal::{IntSize};

use std::fmt;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BaseTy {
    Unit,
    Bool,
    Uint(IntSize),
    Int(IntSize),
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
            Self::Uint(size) => write!(f, "u{}", size),
            Self::Int(size) => write!(f, "i{}", size),
        }
    }
}


