use std::fmt;

use itertools::Itertools;
use liquid_rust_common::index::{Idx, IndexVec};
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hir::def_id::DefId;
pub use rustc_middle::mir::{
    BasicBlock, Local, SourceInfo, SwitchTargets, UnOp, RETURN_PLACE, START_BLOCK,
};
use rustc_middle::{mir, ty::IntTy};

use crate::ty::Ty;

#[derive(Debug)]
pub struct Body<'tcx> {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData>,
    pub arg_count: usize,
    pub nlocals: usize,
    pub mir: &'tcx mir::Body<'tcx>,
}

#[derive(Debug)]
pub struct BasicBlockData {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
}

pub struct Terminator {
    pub kind: TerminatorKind,
    pub source_info: SourceInfo,
}

#[derive(Debug)]
pub enum TerminatorKind {
    Return,
    Call {
        func: DefId,
        substs: Vec<Ty>,
        args: Vec<Operand>,
        destination: Option<(Place, BasicBlock)>,
    },
    SwitchInt {
        discr: Operand,
        targets: SwitchTargets,
    },
    Goto {
        target: BasicBlock,
    },
}

pub struct Statement {
    pub kind: StatementKind,
}

#[derive(Debug)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    Nop,
}

pub enum Rvalue {
    Use(Operand),
    MutRef(Place),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Gt,
    Lt,
}

pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

pub struct Place {
    pub local: Local,
    pub projection: Vec<PlaceElem>,
}

#[derive(Debug)]
pub enum PlaceElem {
    Deref,
}

pub enum Constant {
    Int(i128, IntTy),
    Bool(bool),
}

impl Body<'_> {
    #[inline]
    pub fn args_iter(&self) -> impl ExactSizeIterator<Item = Local> {
        (1..self.arg_count + 1).map(Local::new)
    }

    #[inline]
    pub fn vars_and_temps_iter(&self) -> impl ExactSizeIterator<Item = Local> {
        (self.arg_count + 1..self.nlocals).map(Local::new)
    }

    #[inline]
    pub fn reverse_postorder(&self) -> impl ExactSizeIterator<Item = BasicBlock> + '_ {
        mir::traversal::reverse_postorder(self.mir).map(|(bb, _)| bb)
    }

    #[inline]
    pub fn is_join_point(&self, bb: BasicBlock) -> bool {
        self.mir.predecessors()[bb].len() > 1
    }

    #[inline]
    pub fn dominators(&self) -> Dominators<BasicBlock> {
        self.mir.dominators()
    }

    #[inline]
    pub fn join_points(&self) -> impl Iterator<Item = BasicBlock> + '_ {
        self.basic_blocks
            .indices()
            .filter(|bb| self.is_join_point(*bb))
    }
}

impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StatementKind::Assign(place, rvalue) => {
                write!(f, "{:?} = {:?}", place, rvalue)
            }
            StatementKind::Nop => write!(f, "nop"),
        }
    }
}

impl fmt::Debug for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TerminatorKind::Return => write!(f, "return"),
            TerminatorKind::Call {
                func,
                substs: ty_subst,
                args,
                destination,
            } => {
                if let Some((place, target)) = destination {
                    write!(
                        f,
                        "{:?} = call {:?}({:?}) -> {:?}",
                        place,
                        func,
                        args.iter().format(", "),
                        target
                    )
                } else {
                    write!(
                        f,
                        "call {:?}<{:?}>({:?})",
                        func,
                        ty_subst.iter().format(", "),
                        args.iter().format(", ")
                    )
                }
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                write!(f, "switchInt({:?}) -> [todo]", discr,)
            }
            TerminatorKind::Goto { target } => {
                write!(f, "goto -> {:?}", *target)
            }
        }
    }
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for elem in &self.projection {
            match elem {
                PlaceElem::Deref => write!(f, "*")?,
            }
        }
        write!(f, "{:?}", self.local)
    }
}

impl fmt::Debug for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Use(op) => write!(f, "{:?}", op),
            Self::MutRef(local) => write!(f, "&mut {:?}", local),
            Self::BinaryOp(bin_op, op1, op2) => write!(f, "{:?}({:?}, {:?})", bin_op, op1, op2),
            Self::UnaryOp(un_up, op) => write!(f, "{:?}({:?})", un_up, op),
        }
    }
}

impl fmt::Debug for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Copy(place) => write!(f, "copy {:?}", place),
            Self::Move(place) => write!(f, "move {:?}", place),
            Self::Constant(c) => write!(f, "{:?}", c),
        }
    }
}

impl fmt::Debug for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(n, int_ty) => write!(f, "{}{:?}", n, int_ty),
            Self::Bool(b) => write!(f, "{}", b),
        }
    }
}
