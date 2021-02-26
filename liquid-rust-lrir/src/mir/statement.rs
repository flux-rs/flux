use crate::mir::{Local, Place, Rvalue, SourceInfo};

pub struct Statement {
    pub kind: StatementKind,
    pub source_info: SourceInfo,
}

pub enum StatementKind {
    Assign(Place, Rvalue),
    StorageLive(Local),
    StorageDead(Local),
    Nop,
}
