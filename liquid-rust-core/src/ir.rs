use liquid_rust_common::index::{Idx, IndexVec};
pub use rustc_middle::mir::{BasicBlock, Local};
use rustc_middle::ty::{IntTy, UintTy};

use crate::ty::TypeLayout;

#[derive(Debug)]
pub struct Body {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData>,
    pub arg_count: usize,
    pub local_decls: IndexVec<Local, LocalDecl>,
}

#[derive(Debug)]
pub struct LocalDecl {
    pub layout: TypeLayout,
}

#[derive(Debug)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
}

#[derive(Debug)]
pub struct Terminator {
    pub kind: TerminatorKind,
}

#[derive(Debug)]
pub enum TerminatorKind {
    Return,
}

#[derive(Debug)]
pub struct Statement {
    pub kind: StatementKind,
}

#[derive(Debug)]
pub enum StatementKind {
    Assign(Local, Rvalue),
    Nop,
}

#[derive(Debug)]
pub enum Rvalue {
    Use(Operand),
}

#[derive(Debug)]
pub enum Operand {
    Copy(Local),
    Constant(Constant),
}

#[derive(Debug)]
pub enum Constant {
    Int(i128, IntTy),
    Uint(u128, UintTy),
}

impl Body {
    #[inline]
    pub fn args_iter(&self) -> impl Iterator<Item = Local> {
        (1..self.arg_count + 1).map(Local::new)
    }

    #[inline]
    pub fn vars_and_temps_iter(&self) -> impl Iterator<Item = Local> {
        (self.arg_count + 1..self.local_decls.len()).map(Local::new)
    }
}
