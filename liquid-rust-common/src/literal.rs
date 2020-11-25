use std::fmt;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Literal {
    Unit,
    Bool(bool),
    Uint(u128, IntSize),
    Int(i128, IntSize),
}

impl From<bool> for Literal {
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<()> for Literal {
    fn from((): ()) -> Self {
        Self::Unit
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => "()".fmt(f),
            Self::Bool(b) => b.fmt(f),
            Self::Uint(uint, _) => uint.fmt(f),
            Self::Int(int, _) => int.fmt(f),
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
