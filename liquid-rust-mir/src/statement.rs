use crate::{local::Local, rvalue::Rvalue, Span};

use std::fmt;

pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

pub enum StatementKind {
    Noop,
    Assign(Local, Rvalue),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StatementKind::Noop => "noop".fmt(f),
            StatementKind::Assign(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
        }
    }
}
