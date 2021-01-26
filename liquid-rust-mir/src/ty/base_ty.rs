use crate::ty::{int_sign::IntSign, int_size::IntSize, ty::Ty};

use std::fmt;

/// A base type.
///
/// Each one of these types corresponds to one Rust scalar type.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BaseTy {
    /// The `()` type.
    Unit,
    /// The `bool` type.
    Bool,
    /// The integer types, i.e. `u8`, `i8`, etc.
    Int(IntSign, IntSize),
}

impl BaseTy {
    /// Consume the base type `B` and return the refined type `{b : B | true}`.
    pub fn refined(self) -> Ty {
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
