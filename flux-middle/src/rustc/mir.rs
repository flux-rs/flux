//! A simplified version of rust mir.

use std::fmt;

use flux_common::index::{Idx, IndexVec};
use itertools::Itertools;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir,
    ty::{subst::SubstsRef, FloatTy, IntTy, UintTy},
};
pub use rustc_middle::{
    mir::{BasicBlock, Field, Local, SourceInfo, SwitchTargets, UnOp, RETURN_PLACE, START_BLOCK},
    ty::Variance,
};
use rustc_span::Span;
use rustc_target::abi::VariantIdx;

use super::ty::{GenericArg, Ty};
use crate::intern::List;

pub struct Body<'tcx> {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    pub local_decls: IndexVec<Local, LocalDecl>,
    pub fake_predecessors: IndexVec<BasicBlock, usize>,
    pub(crate) rustc_mir: mir::Body<'tcx>,
}

#[derive(Debug)]
pub struct BasicBlockData<'tcx> {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator<'tcx>>,
    pub is_cleanup: bool,
}

pub struct LocalDecl {
    pub ty: Ty,
    pub source_info: SourceInfo,
}

pub struct Terminator<'tcx> {
    pub kind: TerminatorKind<'tcx>,
    pub source_info: SourceInfo,
}

#[derive(Debug)]
pub struct CallSubsts<'tcx> {
    pub orig: SubstsRef<'tcx>,
    pub lowered: List<GenericArg>,
}

/// An `Instance` is the resolved call-target at a particular trait-call-site
#[derive(Debug)]
pub struct Instance {
    pub impl_f: DefId,
    pub substs: List<GenericArg>,
}

#[derive(Debug)]
pub enum TerminatorKind<'tcx> {
    Return,
    Call {
        func: DefId,
        substs: CallSubsts<'tcx>,
        args: Vec<Operand>,
        destination: Place,
        target: Option<BasicBlock>,
        cleanup: Option<BasicBlock>,
        instance: Option<Instance>,
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
        unwind: Option<BasicBlock>,
    },
    DropAndReplace {
        place: Place,
        value: Operand,
        target: BasicBlock,
        unwind: Option<BasicBlock>,
    },
    Assert {
        cond: Operand,
        expected: bool,
        target: BasicBlock,
        msg: &'static str,
    },
    Unreachable,
    FalseEdge {
        real_target: BasicBlock,
        imaginary_target: BasicBlock,
    },
    FalseUnwind {
        real_target: BasicBlock,
        unwind: Option<BasicBlock>,
    },
    Resume,
}

pub struct Statement {
    pub kind: StatementKind,
    pub source_info: SourceInfo,
}

#[derive(Debug)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    SetDiscriminant(Place, VariantIdx),
    FakeRead(Box<(FakeReadCause, Place)>),
    AscribeUserType(Place, Variance),
    Nop,
}

pub enum Rvalue {
    Use(Operand),
    MutRef(Place),
    ShrRef(Place),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
    Aggregate(AggregateKind, Vec<Operand>),
    Discriminant(Place),
    Len(Place),
    Cast(CastKind, Operand, Ty),
}

#[derive(Copy, Clone)]
pub enum CastKind {
    IntToInt,
    FloatToInt,
    IntToFloat,
}

pub enum AggregateKind {
    Adt(DefId, VariantIdx, List<GenericArg>),
    Array(Ty),
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

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<PlaceElem>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PlaceElem {
    Deref,
    Field(Field),
    Downcast(VariantIdx),
}

pub enum Constant {
    Int(i128, IntTy),
    Uint(u128, UintTy),
    Float(u128, FloatTy),
    Bool(bool),
    /// We only support opaque string slices, so no data stored here for now.
    Str,
    Unit,
}

pub enum FakeReadCause {
    ForLet(Option<LocalDefId>),
    ForMatchedPlace(Option<LocalDefId>),
}

impl<'tcx> Terminator<'tcx> {
    pub fn is_return(&self) -> bool {
        matches!(self.kind, TerminatorKind::Return)
    }
}

impl Statement {
    pub fn is_nop(&self) -> bool {
        matches!(self.kind, StatementKind::Nop)
    }
}

impl<'tcx> Body<'tcx> {
    pub fn span(&self) -> Span {
        self.rustc_mir.span
    }

    #[inline]
    pub fn args_iter(&self) -> impl ExactSizeIterator<Item = Local> {
        (1..self.rustc_mir.arg_count + 1).map(Local::new)
    }

    #[inline]
    pub fn vars_and_temps_iter(&self) -> impl ExactSizeIterator<Item = Local> {
        (self.rustc_mir.arg_count + 1..self.local_decls.len()).map(Local::new)
    }

    #[inline]
    pub fn reverse_postorder<'a>(&'a self) -> impl ExactSizeIterator<Item = BasicBlock> + 'tcx
    where
        'a: 'tcx,
    {
        mir::traversal::reverse_postorder(&self.rustc_mir).map(|(bb, _)| bb)
    }

    #[inline]
    pub fn is_join_point(&self, bb: BasicBlock) -> bool {
        // The entry block is a joint point if it has at least one predecessor because there's
        // an implicit goto from the environment at the beginning of the function.
        let real_preds =
            self.rustc_mir.basic_blocks.predecessors()[bb].len() - self.fake_predecessors[bb];
        real_preds > usize::from(bb != START_BLOCK)
    }

    #[inline]
    pub fn dominators(&self) -> Dominators<BasicBlock> {
        self.rustc_mir.basic_blocks.dominators()
    }

    #[inline]
    pub fn join_points<'a>(&'a self) -> impl Iterator<Item = BasicBlock> + 'tcx
    where
        'a: 'tcx,
    {
        self.basic_blocks
            .indices()
            .filter(|bb| self.is_join_point(*bb))
    }
}

impl Place {
    pub const RETURN: &'static Place = &Place { local: RETURN_PLACE, projection: vec![] };

    pub fn new(local: Local, projection: Vec<PlaceElem>) -> Place {
        Place { local, projection }
    }
}

impl PlaceElem {
    pub fn as_field(&self) -> Option<Field> {
        match self {
            PlaceElem::Field(field) => Some(*field),
            _ => None,
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
            StatementKind::SetDiscriminant(place, variant_idx) => {
                write!(f, "discriminant({:?}) = {:?}", place, variant_idx)
            }
            StatementKind::FakeRead(box (cause, place)) => {
                write!(f, "FakeRead({cause:?}, {place:?})")
            }
            StatementKind::AscribeUserType(place, variance) => {
                write!(f, "AscribeUserType({place:?}, {variance:?})")
            }
        }
    }
}

impl<'tcx> fmt::Debug for Terminator<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TerminatorKind::Return => write!(f, "return"),
            TerminatorKind::Unreachable => write!(f, "unreachable"),
            TerminatorKind::Call { func, substs, args, destination, target, cleanup, .. } => {
                let fname = rustc_middle::ty::tls::with(|tcx| {
                    let path = tcx.def_path(*func);
                    path.data.iter().join("::")
                });
                write!(f, "{destination:?} = call {fname}")?;

                if !substs.lowered.is_empty() {
                    write!(f, "::<{:?}>", substs.lowered.iter().format(", "))?;
                }

                write!(
                    f,
                    "({:?}) -> [return: {target:?}, cleanup: {cleanup:?}]",
                    args.iter().format(", "),
                )
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
            TerminatorKind::DropAndReplace { place, value, target, unwind } => {
                write!(
                    f,
                    "replace({place:?} <- {value:?}) -> [return: {target:?}], unwind: {unwind:?}"
                )
            }
            TerminatorKind::Drop { place, target, unwind } => {
                write!(f, "drop({place:?}) -> [{target:?}, unwind: {unwind:?}]")
            }
            TerminatorKind::Assert { cond, target, expected, msg } => {
                write!(
                    f,
                    "assert({cond:?} is expected to be {expected:?}, \"{msg}\") -> {target:?}"
                )
            }
            TerminatorKind::FalseEdge { real_target, imaginary_target } => {
                write!(f, "falseEdge -> [real: {real_target:?}, imaginary: {imaginary_target:?}]")
            }
            TerminatorKind::FalseUnwind { real_target, unwind } => {
                write!(f, "falseUnwind -> [real: {real_target:?}, cleanup: {unwind:?}]")
            }
            TerminatorKind::Resume => write!(f, "resume"),
        }
    }
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut p = format!("{:?}", self.local);
        let mut need_parens = false;
        for elem in &self.projection {
            match elem {
                PlaceElem::Field(f) => {
                    if need_parens {
                        p = format!("({p}).{}", u32::from(*f));
                        need_parens = false;
                    } else {
                        p = format!("{p}.{}", u32::from(*f));
                    }
                }
                PlaceElem::Deref => {
                    p = format!("*{p}");
                    need_parens = true;
                }
                PlaceElem::Downcast(variant_idx) => {
                    p = format!("{p} as {variant_idx:?}");
                    need_parens = true;
                }
            }
        }
        write!(f, "{}", p)
    }
}

impl fmt::Debug for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rvalue::Use(op) => write!(f, "{:?}", op),
            Rvalue::MutRef(place) => write!(f, "&mut {:?}", place),
            Rvalue::ShrRef(place) => write!(f, "& {:?}", place),
            Rvalue::Discriminant(place) => write!(f, "discriminant({:?})", place),
            Rvalue::BinaryOp(bin_op, op1, op2) => write!(f, "{:?}({:?}, {:?})", bin_op, op1, op2),
            Rvalue::UnaryOp(un_up, op) => write!(f, "{:?}({:?})", un_up, op),
            Rvalue::Aggregate(AggregateKind::Adt(def_id, variant_idx, substs), args) => {
                let fname = rustc_middle::ty::tls::with(|tcx| {
                    let path = tcx.def_path(*def_id);
                    path.data.iter().join("::")
                });
                if substs.is_empty() {
                    write!(f, "{fname}::{variant_idx:?}({:?})", args.iter().format(", "))
                } else {
                    write!(
                        f,
                        "{fname}::{variant_idx:?}::<{:?}>({:?})",
                        substs.iter().format(", "),
                        args.iter().format(", ")
                    )
                }
            }
            Rvalue::Aggregate(AggregateKind::Array(_), args) => {
                write!(f, "[{:?}]", args.iter().format(", "))
            }
            Rvalue::Len(place) => write!(f, "Len({place:?})"),
            Rvalue::Cast(kind, op, ty) => write!(f, "{op:?} as {ty:?} [{kind:?}]"),
        }
    }
}

impl fmt::Debug for CastKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CastKind::IntToInt => write!(f, "IntToInt"),
            CastKind::FloatToInt => write!(f, "FloatToInt"),
            CastKind::IntToFloat => write!(f, "IntToFloat"),
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
            Constant::Int(n, int_ty) => write!(f, "{}{}", n, int_ty.name_str()),
            Constant::Uint(n, uint_ty) => write!(f, "{}{}", n, uint_ty.name_str()),
            Constant::Float(bits, float_ty) => write!(f, "{}{}", bits, float_ty.name_str()),
            Constant::Bool(b) => write!(f, "{}", b),
            Constant::Unit => write!(f, "()"),
            Constant::Str => write!(f, "\"<opaque str>\""),
        }
    }
}

impl fmt::Debug for FakeReadCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FakeReadCause::ForLet(def_id) => write!(f, "ForLet({def_id:?})"),
            FakeReadCause::ForMatchedPlace(def_id) => write!(f, "ForMatchedPlace({def_id:?})"),
        }
    }
}
