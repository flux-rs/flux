use crate::{local::Local, rvalue::Rvalue};

use std::fmt;

pub struct Statement<S> {
    pub kind: StatementKind,
    pub span: S,
}

pub enum StatementKind {
    Noop,
    Assign(Local, Rvalue),
}

impl<S> fmt::Display for Statement<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StatementKind::Noop => "noop".fmt(f),
            StatementKind::Assign(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
        }
    }
}
