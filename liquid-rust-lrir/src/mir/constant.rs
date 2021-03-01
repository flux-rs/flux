use crate::ty::BaseTy;

use std::fmt;

/// A typed constant.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Constant {
    /// The bit layout of the constant based on Rust's data layout, e.g. `true` is represented as
    /// `1`, `false` is represented as `0`.
    bits: u128,
    /// The type of the constant.
    ty: BaseTy,
}

impl Constant {
    /// return the type of the constant
    pub fn ty(&self) -> BaseTy {
        self.ty
    }

    /// Check if the literal is identical to `true`.
    pub const fn is_true(&self) -> bool {
        matches!(self.ty, BaseTy::Bool) && self.bits == 1
    }

    pub const fn new(bits: u128, ty: BaseTy) -> Self {
        Self { bits, ty }
    }
}

impl From<bool> for Constant {
    fn from(b: bool) -> Self {
        Self {
            bits: b as u128,
            ty: BaseTy::Bool,
        }
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ty {
            BaseTy::Bool => write!(f, "{}", self.bits != 0),
            BaseTy::Int => write!(f, "{}", self.bits),
        }
    }
}
