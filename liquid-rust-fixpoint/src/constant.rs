use std::fmt;

pub enum Constant {
    Bool(bool),
    Int(u128),
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(bool) => bool.fmt(f),
            Self::Int(int) => int.fmt(f),
        }
    }
}
