use crate::{statement::Statement, terminator::Terminator};

use liquid_rust_common::new_index;

use std::fmt;

new_index! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    BBlockId
}

impl BBlockId {
    pub const fn start() -> Self {
        Self(0)
    }
}

impl fmt::Display for BBlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

pub struct BBlock {
    statements: Box<[Statement]>,
    terminator: Terminator,
    predecessors: Box<[BBlockId]>,
}

impl BBlock {
    pub fn statements(&self) -> &[Statement] {
        self.statements.as_ref()
    }

    pub fn terminator(&self) -> &Terminator {
        &self.terminator
    }

    pub fn predecessors(&self) -> &[BBlockId] {
        self.predecessors.as_ref()
    }
}

impl BBlock {
    pub fn builder() -> BBlockBuilder {
        BBlockBuilder {
            statements: Vec::new(),
            terminator: None,
            predecessors: Vec::new(),
        }
    }
}

pub struct BBlockBuilder {
    statements: Vec<Statement>,
    terminator: Option<Terminator>,
    predecessors: Vec<BBlockId>,
}

impl BBlockBuilder {
    pub fn add_terminator(&mut self, terminator: Terminator) {
        self.terminator = Some(terminator);
    }

    pub fn add_statement(&mut self, statement: Statement) {
        self.statements.push(statement);
    }

    pub fn add_predecessor(&mut self, predecessor: BBlockId) {
        self.predecessors.push(predecessor);
    }

    pub fn build(self) -> Option<BBlock> {
        Some(BBlock {
            statements: self.statements.into_boxed_slice(),
            terminator: self.terminator?,
            predecessors: self.predecessors.into_boxed_slice(),
        })
    }
}
