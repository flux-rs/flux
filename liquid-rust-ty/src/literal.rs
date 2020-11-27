use crate::base_ty::BaseTy;

use std::fmt;

#[derive(Debug, Clone, Copy)]
pub struct Literal {
    bits: u128,
    ty: BaseTy,
}

impl Literal {
    pub const fn new(bits: u128, ty: BaseTy) -> Self {
        Self { bits, ty }
    }

    pub const fn base_ty(&self) -> BaseTy {
        self.ty
    }

    pub const fn is_true(&self) -> bool {
        matches!(self.ty, BaseTy::Bool) && self.bits != 0
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
                Self::new(integer as u128, BaseTy::Int(Sign::$sign, IntSize::$size))
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
                Sign::Signed => (self.bits as i128).fmt(f),
                Sign::Unsigned => self.bits.fmt(f),
            },
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Sign {
    Signed,
    Unsigned,
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice = match self {
            Self::Signed => "i",
            Self::Unsigned => "u",
        };

        slice.fmt(f)
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum IntSize {
    Size8,
    Size16,
    Size32,
    Size64,
    Size128,
    SizePtr,
}

impl fmt::Display for IntSize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice = match self {
            Self::Size8 => "8",
            Self::Size16 => "16",
            Self::Size32 => "32",
            Self::Size64 => "64",
            Self::Size128 => "128",
            Self::SizePtr => "size",
        };

        slice.fmt(f)
    }
}
