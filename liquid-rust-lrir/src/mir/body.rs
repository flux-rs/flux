use crate::mir::{Local, LocalDecl, BasicBlock, BasicBlockData, Span};

use std::collections::HashMap;

pub struct Body {
    basic_blocks: HashMap<BasicBlock, BasicBlockData>,
    pub local_decls: HashMap<Local, LocalDecl>,
    pub arg_count: usize,
    pub span: Span,
    predecessors: HashMap<BasicBlock, Vec<BasicBlock>>,
}
