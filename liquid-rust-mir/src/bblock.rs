use crate::{statement::Statement, terminator::Terminator};

use liquid_rust_common::new_index;

use std::fmt;

new_index! {
    #[derive(Clone, Copy, Debug)]
    BBlockId
}

impl fmt::Display for BBlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

pub struct BBlock<S> {
    statements: Box<[Statement<S>]>,
    terminator: Terminator<S>,
}

impl<S> BBlock<S> {
    pub fn statements(&self) -> &[Statement<S>] {
        self.statements.as_ref()
    }

    pub fn terminator(&self) -> &Terminator<S> {
        &self.terminator
    }
}

impl<S> BBlock<S> {
    pub fn builder() -> BBlockBuilder<S> {
        BBlockBuilder {
            statements: Vec::new(),
            terminator: None,
        }
    }
}

pub struct BBlockBuilder<S> {
    statements: Vec<Statement<S>>,
    terminator: Option<Terminator<S>>,
}

impl<S> BBlockBuilder<S> {
    pub fn add_terminator(&mut self, terminator: Terminator<S>) {
        self.terminator = Some(terminator);
    }

    pub fn add_statement(&mut self, statement: Statement<S>) {
        self.statements.push(statement);
    }

    pub fn build(self) -> Option<BBlock<S>> {
        Some(BBlock {
            statements: self.statements.into_boxed_slice(),
            terminator: self.terminator?,
        })
    }
}
