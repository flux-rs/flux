use liquid_rust_common::index::{Idx, IndexVec};
use rustc_hir::def_id::DefId;
pub use rustc_middle::mir::{BasicBlock, Local};
use rustc_middle::{mir::SourceInfo, ty::IntTy};

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
    pub source_info: SourceInfo,
}

#[derive(Debug)]
pub enum TerminatorKind {
    Return,
    Call {
        func: DefId,
        args: Vec<Operand>,
        destination: Option<(Place, BasicBlock)>,
    },
}

#[derive(Debug)]
pub struct Statement {
    pub kind: StatementKind,
}

#[derive(Debug)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    Nop,
}

#[derive(Debug)]
pub enum Rvalue {
    Use(Operand),
    MutRef(Local),
    BinaryOp(BinOp, Operand, Operand),
}

#[derive(Debug)]
pub enum BinOp {
    Add,
}

#[derive(Debug)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

#[derive(Debug)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<PlaceElem>,
}

#[derive(Debug)]
pub enum PlaceElem {
    Deref,
}

#[derive(Debug)]
pub enum Constant {
    Int(i128, IntTy),
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
