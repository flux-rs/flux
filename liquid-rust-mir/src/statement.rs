use crate::{local::Local, rvalue::Rvalue};

use std::fmt;

pub enum Statement {
    Noop,
    Assign(Local, Rvalue),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Noop => "noop".fmt(f),
            Self::Assign(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
        }
    }
}
