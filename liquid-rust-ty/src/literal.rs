use crate::{base_ty::BaseTy, int_sign::IntSign, int_size::IntSize};

use std::fmt;
/// A typed literal.
///
/// Used to represent constants inside predicates.
#[derive(Debug, Clone, Copy)]
pub struct Literal {
    /// The bit layout of the literal based on Rust's data layout, e.g. `true` is represented as
    /// `1`, `false` is represented as `0`.
    bits: u128,
    /// The type of the literal.
    ty: BaseTy,
}

impl Literal {
    /// Create a new literal from a bit layout and a base type. Creating a literal with an invalid
    /// layout for its type is unsound.
    pub const fn new(bits: u128, ty: BaseTy) -> Self {
        Self { bits, ty }
    }

    /// Return the type of the literal.
    pub const fn base_ty(&self) -> BaseTy {
        self.ty
    }

    /// Check if the literal is identical to `true`.
    pub const fn is_true(&self) -> bool {
        matches!(self.ty, BaseTy::Bool) && self.bits == 1
    }
}

impl From<bool> for Literal {
    fn from(b: bool) -> Self {
        Self::new(b as u128, BaseTy::Bool)
    }
}

impl From<()> for Literal {
    fn from((): ()) -> Self {
        Self::new(0, BaseTy::Unit)
    }
}

macro_rules! impl_from_num {
    ($ty:ident, $sign:ident, $size:ident) => {
        impl From<$ty> for Literal {
            fn from(integer: $ty) -> Self {
                Self::new(integer as u128, BaseTy::Int(IntSign::$sign, IntSize::$size))
            }
        }
    };
}

impl_from_num!(u8, Unsigned, Size8);
impl_from_num!(u16, Unsigned, Size16);
impl_from_num!(u32, Unsigned, Size32);
impl_from_num!(u64, Unsigned, Size64);
impl_from_num!(u128, Unsigned, Size128);
impl_from_num!(usize, Unsigned, SizePtr);
impl_from_num!(i8, Signed, Size8);
impl_from_num!(i16, Signed, Size16);
impl_from_num!(i32, Signed, Size32);
impl_from_num!(i64, Signed, Size64);
impl_from_num!(i128, Signed, Size128);
impl_from_num!(isize, Signed, SizePtr);

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ty {
            BaseTy::Unit => "()".fmt(f),
            BaseTy::Bool => (self.bits != 0).fmt(f),
            BaseTy::Int(sign, _) => match sign {
                IntSign::Signed => (self.bits as i128).fmt(f),
                IntSign::Unsigned => self.bits.fmt(f),
            },
        }
    }
}
