use std::fmt;

pub struct Variable;

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v")
    }
}

crate::impl_emit_by_display!(Variable);
