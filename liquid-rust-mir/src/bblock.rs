use crate::{
    local::Local,
    statement::{Statement, StatementKind},
    terminator::Terminator,
};

use liquid_rust_common::{index::IndexMap, new_index};

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
    closed_locals: Box<[Local]>,
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

    pub fn closed_locals(&self) -> &[Local] {
        self.closed_locals.as_ref()
    }
}

impl BBlock {
    pub fn builder(len_locals: usize) -> BBlockBuilder {
        BBlockBuilder {
            statements: Vec::new(),
            terminator: None,
            predecessors: Vec::new(),
            locals: IndexMap::from_raw(vec![LocalState::Unknown; len_locals]),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LocalState {
    Alive,
    Dead,
    Unknown,
}

impl LocalState {
    fn live(&mut self) {
        *self = Self::Alive;
    }

    fn dead(&mut self) {
        match self {
            Self::Alive => *self = Self::Dead,
            Self::Dead => *self = Self::Dead,
            Self::Unknown => (),
        }
    }
}

pub struct BBlockBuilder {
    statements: Vec<Statement>,
    terminator: Option<Terminator>,
    predecessors: Vec<BBlockId>,
    locals: IndexMap<Local, LocalState>,
}

impl BBlockBuilder {
    pub fn add_terminator(&mut self, terminator: Terminator) {
        self.terminator = Some(terminator);
    }

    pub fn add_statement(&mut self, statement: Statement) {
        match &statement.kind {
            StatementKind::StorageLive(local) => self.locals.get_mut(*local).unwrap().live(),
            StatementKind::StorageDead(local) => self.locals.get_mut(*local).unwrap().dead(),
            _ => (),
        }

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
            closed_locals: self
                .locals
                .into_iter()
                .filter_map(|(local, state)| (state == LocalState::Dead).then(|| local))
                .collect(),
        })
    }
}
