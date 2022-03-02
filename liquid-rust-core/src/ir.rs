use std::fmt;

use itertools::Itertools;
use liquid_rust_common::index::{Idx, IndexVec};
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hir::def_id::DefId;
pub use rustc_middle::mir::{
    BasicBlock, Local, SourceInfo, SwitchTargets, UnOp, RETURN_PLACE, START_BLOCK,
};
use rustc_middle::{
    mir,
    ty::{FloatTy, IntTy, UintTy},
};

use crate::ty::Ty;

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
    Drop {
        place: Place,
        target: BasicBlock,
    },
    Assert {
        cond: Operand,
        expected: bool,
        target: BasicBlock,
    },
}

pub struct Statement {
    pub kind: StatementKind,
    pub source_info: SourceInfo,
}

#[derive(Debug)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    Nop,
}

pub enum Rvalue {
    Use(Operand),
    MutRef(Place),
    ShrRef(Place),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Gt,
    Ge,
    Lt,
    Le,
    Eq,
    Ne,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
}

pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

pub enum Place {
    /// x
    Local(Local),
    /// *x
    Deref(Local),
}

// pub struct Place {
//     pub local: Local,
//     pub projection: Vec<PlaceElem>,
// }

// #[derive(Debug)]
// pub enum PlaceElem {
//     Deref,
// }

pub enum Constant {
    Int(i128, IntTy),
    Uint(u128, UintTy),
    Float(u128, FloatTy),
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
        // The entry block is a joint point if it has at least one predecessor because there's
        // an implicit goto from the environment at the beginning of the function.
        self.mir.predecessors()[bb].len() > (if bb == START_BLOCK { 0 } else { 1 })
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

impl Place {
    pub fn local(&self) -> Local {
        match self {
            Place::Local(local) | Place::Deref(local) => *local,
        }
    }
}

impl fmt::Debug for Body<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (bb, data) in self.basic_blocks.iter_enumerated() {
            writeln!(
                f,
                "{bb:?}: {{{}",
                data.statements
                    .iter()
                    .filter(|stmt| !matches!(stmt.kind, StatementKind::Nop))
                    .format_with("", |stmt, f| f(&format_args!("\n    {stmt:?};")))
            )?;
            if let Some(terminator) = &data.terminator {
                writeln!(f, "    {terminator:?}", terminator = terminator)?;
            }
            writeln!(f, "}}\n")?;
        }
        Ok(())
    }
}

impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StatementKind::Assign(place, rvalue) => write!(f, "{:?} = {:?}", place, rvalue),
            StatementKind::Nop => write!(f, "nop"),
        }
    }
}

impl fmt::Debug for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TerminatorKind::Return => write!(f, "return"),
            TerminatorKind::Call { func, substs: ty_subst, args, destination } => {
                let fname = rustc_middle::ty::tls::with(|tcx| {
                    let path = tcx.def_path(*func);
                    path.data.iter().join("::")
                });
                if let Some((place, target)) = destination {
                    write!(
                        f,
                        "{:?} = call {}({:?}) -> {:?}",
                        place,
                        fname,
                        args.iter().format(", "),
                        target
                    )
                } else {
                    write!(
                        f,
                        "call {}<{:?}>({:?})",
                        fname,
                        ty_subst.iter().format(", "),
                        args.iter().format(", ")
                    )
                }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                write!(
                    f,
                    "switchInt({discr:?}) -> [{}, otherwise: {:?}]",
                    targets
                        .iter()
                        .format_with(", ", |(val, bb), f| f(&format_args!("{:?}: {:?}", val, bb))),
                    targets.otherwise()
                )
            }
            TerminatorKind::Goto { target } => {
                write!(f, "goto -> {target:?}")
            }
            TerminatorKind::Drop { place, target } => {
                write!(f, "drop({place:?}) -> {target:?}")
            }
            TerminatorKind::Assert { cond, target, expected } => {
                write!(f, "assert({cond:?} is expected to be {expected:?}) -> {target:?}")
            }
        }
    }
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Place::Local(local) => write!(f, "{local:?}"),
            Place::Deref(local) => write!(f, "*{local:?}"),
        }
        // for elem in &self.projection {
        //     match elem {
        //         PlaceElem::Deref => write!(f, "*")?,
        //     }
        // }
        // write!(f, "{:?}", self.local)
    }
}

impl fmt::Debug for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Use(op) => write!(f, "{:?}", op),
            Self::MutRef(place) => write!(f, "&mut {:?}", place),
            Self::ShrRef(place) => write!(f, "& {:?}", place),
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
            Self::Int(n, int_ty) => write!(f, "{}{}", n, int_ty.name_str()),
            Self::Uint(n, uint_ty) => write!(f, "{}{}", n, uint_ty.name_str()),
            Self::Float(bits, float_ty) => write!(f, "{}{}", bits, float_ty.name_str()),
            Self::Bool(b) => write!(f, "{}", b),
        }
    }
}
