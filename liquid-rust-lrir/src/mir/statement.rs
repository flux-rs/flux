use crate::mir::{Local, Place, Rvalue, Span};

pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

pub enum StatementKind {
    Assign(Place, Rvalue),
    StorageLive(Local),
    StorageDead(Local),
    Nop,
}
