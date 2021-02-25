use crate::{local::Local, rvalue::Rvalue, Span};

use std::fmt;

pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

pub enum StatementKind {
    Noop,
    StorageLive(Local),
    StorageDead(Local),
    Assign(Local, Rvalue),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StatementKind::Noop => "noop".fmt(f),
            StatementKind::StorageLive(local) => write!(f, "live({})", local),
            StatementKind::StorageDead(local) => write!(f, "dead({})", local),
            StatementKind::Assign(lhs, rhs) => write!(f, "{} = {}", lhs, rhs),
        }
    }
}
