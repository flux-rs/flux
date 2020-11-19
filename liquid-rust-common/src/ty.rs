use std::fmt::{Display, Formatter, Result};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BaseTy {
    Unit,
    Bool,
    Uint(IntSize),
    Int(IntSize),
}

impl Display for BaseTy {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::Unit => "()".fmt(f),
            Self::Bool => "bool".fmt(f),
            Self::Uint(size) => write!(f, "u{}", size),
            Self::Int(size) => write!(f, "i{}", size),
        }
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

impl Display for IntSize {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
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
