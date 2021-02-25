use std::fmt;

pub enum Sort {
    Int,
    Bool,
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => "bool".fmt(f),
            Self::Int => "int".fmt(f),
        }
    }
}

crate::impl_emit_by_display!(Sort);
