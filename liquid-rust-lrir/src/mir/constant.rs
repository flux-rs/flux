use crate::ty::BaseTy;

use std::fmt;

/// A typed constant.
///
/// FIXME: maybe having this as an enum is better as we don't need to play with the bits to figure
/// out how to lower this as a fixpoint constant.
///
/// The size of the enum would be the same because it would need 1 byte for the discriminant (which
/// is the size of BaseTy) plus the size of the largest variant (which would be a 128-bit integer
/// just like bits).
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

    pub const fn bits(&self) -> u128 {
        self.bits
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

impl From<u128> for Constant {
    fn from(i: u128) -> Self {
        Self {
            bits: i,
            ty: BaseTy::Int,
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
