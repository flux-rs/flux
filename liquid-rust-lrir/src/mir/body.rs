use crate::mir::{BasicBlock, BasicBlockData, Local, LocalDecl, Span};

use liquid_rust_common::index::{Index, IndexMap};

pub struct Body<'tcx> {
    pub basic_blocks: IndexMap<BasicBlock, BasicBlockData>,
    pub local_decls: IndexMap<Local, LocalDecl<'tcx>>,
    pub arg_count: usize,
    pub span: Span,
    pub predecessors: IndexMap<BasicBlock, Vec<BasicBlock>>,
}

impl Body<'_> {
    /// Returns an iterator over all function arguments.
    #[inline]
    pub fn args_iter(&self) -> impl Iterator<Item = Local> {
        let arg_count = self.arg_count;
        (1..arg_count + 1).map(Local::new)
    }

    /// Returns an iterator over all user-defined variables and compiler-generated temporaries (all
    /// locals that are neither arguments nor the return place).
    #[inline]
    pub fn vars_and_temps_iter(&self) -> impl Iterator<Item = Local> {
        let arg_count = self.arg_count;
        let local_count = self.local_decls.len();
        (arg_count + 1..local_count).map(Local::new)
    }
}
