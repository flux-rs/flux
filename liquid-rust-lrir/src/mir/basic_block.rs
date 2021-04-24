use crate::mir::{Statement, Terminator};

pub use rustc_middle::mir::BasicBlock;

pub struct BasicBlockData<'tcx> {
    pub statements: Vec<Statement>,
    pub terminator: Terminator<'tcx>,
}
