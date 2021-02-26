use crate::mir::{Statement, Terminator};

use liquid_rust_common::new_index;

new_index! {
    BasicBlock
}

pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}
