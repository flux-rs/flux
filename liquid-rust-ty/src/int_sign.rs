use std::fmt;

/// The sign of an integer type.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum IntSign {
    /// Signed integer.
    Signed,
    /// Unsigned integer.
    Unsigned,
}

impl fmt::Display for IntSign {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slice = match self {
            Self::Signed => "i",
            Self::Unsigned => "u",
        };

        slice.fmt(f)
    }
}
