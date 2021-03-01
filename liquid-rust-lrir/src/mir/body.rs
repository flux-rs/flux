use crate::mir::{BasicBlock, BasicBlockData, Local, LocalDecl, Span};

use liquid_rust_common::index::IndexMap;

pub struct Body {
    pub basic_blocks: IndexMap<BasicBlock, BasicBlockData>,
    pub local_decls: IndexMap<Local, LocalDecl>,
    pub arg_count: usize,
    pub span: Span,
    pub predecessors: IndexMap<BasicBlock, Vec<BasicBlock>>,
}
