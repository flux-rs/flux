use std::fmt;

/// The size of an integer type.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum IntSize {
    /// 8-bit size.
    Size8,
    /// 16-bit size.
    Size16,
    /// 32-bit size.
    Size32,
    /// 64-bit size.
    Size64,
    /// 128-bit size.
    Size128,
    /// pointer size, i.e. the size of `usize` and `isize`.
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
