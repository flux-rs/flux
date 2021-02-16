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
}

impl BBlock {
    pub fn statements(&self) -> &[Statement] {
        self.statements.as_ref()
    }

    pub fn terminator(&self) -> &Terminator {
        &self.terminator
    }
}

impl BBlock {
    pub fn builder() -> BBlockBuilder {
        BBlockBuilder {
            statements: Vec::new(),
            terminator: None,
        }
    }
}

pub struct BBlockBuilder {
    statements: Vec<Statement>,
    terminator: Option<Terminator>,
}

impl BBlockBuilder {
    pub fn add_terminator(&mut self, terminator: Terminator) {
        self.terminator = Some(terminator);
    }

    pub fn add_statement(&mut self, statement: Statement) {
        self.statements.push(statement);
    }

    pub fn build(self) -> Option<BBlock> {
        Some(BBlock {
            statements: self.statements.into_boxed_slice(),
            terminator: self.terminator?,
        })
    }
}
