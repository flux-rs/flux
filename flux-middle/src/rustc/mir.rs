//! A simplified version of rust mir.

use std::fmt;

use flux_common::{
    bug,
    index::{Idx, IndexVec},
};
use itertools::Itertools;
pub use rustc_abi::FieldIdx;
use rustc_borrowck::BodyWithBorrowckFacts;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexSlice;
use rustc_macros::{Decodable, Encodable};
use rustc_middle::{
    mir,
    ty::{subst::SubstsRef, FloatTy, IntTy, UintTy},
};
pub use rustc_middle::{
    mir::{
        BasicBlock, Local, Location, SourceInfo, SwitchTargets, UnOp, UnwindAction, RETURN_PLACE,
        START_BLOCK,
    },
    ty::Variance,
};
use rustc_span::{Span, Symbol};
pub use rustc_target::abi::{VariantIdx, FIRST_VARIANT};

use super::ty::{GenericArg, Region, Ty, TyKind};
use crate::{
    global_env::GlobalEnv, intern::List, queries::QueryResult, rustc::ty::region_to_string,
};

pub struct Body<'tcx> {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    pub local_decls: IndexVec<Local, LocalDecl>,
    pub fake_predecessors: IndexVec<BasicBlock, usize>,
    pub(crate) body_with_facts: BodyWithBorrowckFacts<'tcx>,
}

#[derive(Debug)]
pub struct BasicBlockData<'tcx> {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator<'tcx>>,
    pub is_cleanup: bool,
}

pub type LocalDecls = IndexSlice<Local, LocalDecl>;

#[derive(Clone)]
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
        unwind: UnwindAction,
        resolved_call: (DefId, CallSubsts<'tcx>),
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
        unwind: UnwindAction,
    },
    Assert {
        cond: Operand,
        expected: bool,
        target: BasicBlock,
        msg: AssertKind,
    },
    Unreachable,
    FalseEdge {
        real_target: BasicBlock,
        imaginary_target: BasicBlock,
    },
    FalseUnwind {
        real_target: BasicBlock,
        unwind: UnwindAction,
    },
    Resume,
}

#[derive(Debug)]
pub enum AssertKind {
    BoundsCheck,
    RemainderByZero,
    Overflow(BinOp),
    DivisionByZero,
    // OverflowNeg(O),
    // ResumedAfterReturn(GeneratorKind),
    // ResumedAfterPanic(GeneratorKind),
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
    PlaceMention(Place),
    Nop,
}

pub enum Rvalue {
    Use(Operand),
    Ref(Region, BorrowKind, Place),
    BinaryOp(BinOp, Operand, Operand),
    CheckedBinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
    Aggregate(AggregateKind, Vec<Operand>),
    Discriminant(Place),
    Len(Place),
    Cast(CastKind, Operand, Ty),
}

pub enum BorrowKind {
    Mut { allow_two_phase_borrow: bool },
    Shared,
}

#[derive(Copy, Clone)]
pub enum CastKind {
    IntToInt,
    FloatToInt,
    IntToFloat,
    Pointer(PointerCast),
}

#[derive(Copy, Clone)]
pub enum PointerCast {
    MutToConstPointer,
}

#[derive(Debug)]
pub enum AggregateKind {
    Adt(DefId, VariantIdx, List<GenericArg>),
    Array(Ty),
    Tuple,
    Closure(DefId, List<GenericArg>),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
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
    BitOr,
    Shl,
    Shr,
}

pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

#[derive(Clone, PartialEq, Eq, Hash, Encodable, Decodable)]
pub struct Place {
    /// the "root" of the place, e.g. `_1` in `*_1.f.g.h`
    pub local: Local,
    /// path taken to "get" the place e.g. `*.f.g.h` in `*_1.f.g.h` (except also have derefs)
    pub projection: Vec<PlaceElem>,
}

#[derive(Debug)]
pub struct PlaceTy {
    pub ty: Ty,
    /// Downcast to a particular variant of an enum or a generator, if included.
    pub variant_index: Option<VariantIdx>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum PlaceElem {
    Deref,
    Field(FieldIdx),
    Downcast(Option<Symbol>, VariantIdx),
    Index(Local),
}

pub enum Constant {
    Int(i128, IntTy),
    Uint(u128, UintTy),
    Float(u128, FloatTy),
    Bool(bool),
    /// We only support opaque string slices, so no data stored here for now.
    Str,
    /// We only support opaque chars, so no data stored here for now
    Char,
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
        self.body_with_facts.body.span
    }

    #[inline]
    pub fn args_iter(&self) -> impl ExactSizeIterator<Item = Local> {
        (1..self.body_with_facts.body.arg_count + 1).map(Local::new)
    }

    #[inline]
    pub fn vars_and_temps_iter(&self) -> impl ExactSizeIterator<Item = Local> {
        (self.body_with_facts.body.arg_count + 1..self.local_decls.len()).map(Local::new)
    }

    #[inline]
    pub fn reverse_postorder<'a>(&'a self) -> impl ExactSizeIterator<Item = BasicBlock> + 'tcx
    where
        'a: 'tcx,
    {
        mir::traversal::reverse_postorder(&self.body_with_facts.body).map(|(bb, _)| bb)
    }

    #[inline]
    pub fn is_join_point(&self, bb: BasicBlock) -> bool {
        let total_preds = self.body_with_facts.body.basic_blocks.predecessors()[bb].len();
        let real_preds = total_preds - self.fake_predecessors[bb];
        // The entry block is a joint point if it has at least one predecessor because there's
        // an implicit goto from the environment at the beginning of the function.
        real_preds > usize::from(bb != START_BLOCK)
    }

    #[inline]
    pub fn dominators(&self) -> Dominators<BasicBlock> {
        self.body_with_facts.body.basic_blocks.dominators()
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

    pub fn ty(&self, genv: &GlobalEnv, local_decls: &LocalDecls) -> QueryResult<PlaceTy> {
        self.projection
            .iter()
            .try_fold(PlaceTy::from_ty(local_decls[self.local].ty.clone()), |place_ty, elem| {
                place_ty.projection_ty(genv, *elem)
            })
    }
}

impl PlaceTy {
    fn from_ty(ty: Ty) -> PlaceTy {
        PlaceTy { ty, variant_index: None }
    }

    fn projection_ty(&self, genv: &GlobalEnv, elem: PlaceElem) -> QueryResult<PlaceTy> {
        if self.variant_index.is_some() && !matches!(elem, PlaceElem::Field(..)) {
            bug!("cannot use non field projection on downcasted place");
        }
        let place_ty = match elem {
            PlaceElem::Deref => PlaceTy::from_ty(self.ty.deref()),
            PlaceElem::Field(fld) => PlaceTy::from_ty(self.field_ty(genv, fld)?),
            PlaceElem::Downcast(_, variant_idx) => {
                PlaceTy { ty: self.ty.clone(), variant_index: Some(variant_idx) }
            }
            PlaceElem::Index(_) => {
                if let TyKind::Array(ty, _) | TyKind::Slice(ty) = self.ty.kind() {
                    PlaceTy::from_ty(ty.clone())
                } else {
                    bug!("index of no-array non-slice {self:?}")
                }
            }
        };
        Ok(place_ty)
    }

    fn field_ty(&self, genv: &GlobalEnv, f: FieldIdx) -> QueryResult<Ty> {
        match self.ty.kind() {
            TyKind::Adt(adt_def, substs) => {
                let variant_def = match self.variant_index {
                    None => adt_def.non_enum_variant(),
                    Some(variant_index) => {
                        assert!(adt_def.is_enum());
                        adt_def.variant(variant_index)
                    }
                };
                let field_def = &variant_def.fields[f];
                let ty = genv.lower_type_of(field_def.did)?;
                Ok(ty.subst(substs))
            }
            TyKind::Tuple(tys) => Ok(tys[f.index()].clone()),
            _ => bug!("extracting field of non-tuple non-adt: {self:?}"),
        }
    }
}

impl PlaceElem {
    pub fn as_field(&self) -> Option<FieldIdx> {
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
                writeln!(f, "    {terminator:?}")?;
            }
            writeln!(f, "}}\n")?;
        }
        Ok(())
    }
}

impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            StatementKind::Assign(place, rvalue) => write!(f, "{place:?} = {rvalue:?}"),
            StatementKind::Nop => write!(f, "nop"),
            StatementKind::PlaceMention(place) => {
                write!(f, "PlaceMention({place:?})")
            }
            StatementKind::SetDiscriminant(place, variant_idx) => {
                write!(f, "discriminant({place:?}) = {variant_idx:?}")
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
            TerminatorKind::Call { func, substs, args, destination, target, unwind, .. } => {
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
                    "({args:?}) -> [return: {target}, unwind: {unwind:?}]",
                    args = args.iter().format(", "),
                    target = opt_bb_to_str(*target),
                )
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                write!(
                    f,
                    "switchInt({discr:?}) -> [{}, otherwise: {:?}]",
                    targets
                        .iter()
                        .format_with(", ", |(val, bb), f| f(&format_args!("{val:?}: {bb:?}"))),
                    targets.otherwise()
                )
            }
            TerminatorKind::Goto { target } => {
                write!(f, "goto -> {target:?}")
            }
            TerminatorKind::Drop { place, target, unwind } => {
                write!(f, "drop({place:?}) -> [{target:?}, unwind: {unwind:?}]",)
            }
            TerminatorKind::Assert { cond, target, expected, msg } => {
                write!(
                    f,
                    "assert({cond:?} is expected to be {expected:?}, \"{msg:?}\") -> {target:?}"
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
                PlaceElem::Downcast(variant_name, variant_idx) => {
                    if let Some(variant_name) = variant_name {
                        p = format!("{p} as {variant_name}");
                    } else {
                        p = format!("{p} as {variant_idx:?}");
                    }
                    need_parens = true;
                }
                PlaceElem::Index(v) => {
                    p = format!("{p}[{v:?}]");
                    need_parens = false;
                }
            }
        }
        write!(f, "{p}")
    }
}

impl fmt::Debug for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rvalue::Use(op) => write!(f, "{op:?}"),
            Rvalue::Ref(r, BorrowKind::Mut { .. }, place) => {
                write!(f, "&{} mut {place:?}", region_to_string(*r))
            }
            Rvalue::Ref(r, BorrowKind::Shared, place) => {
                write!(f, "&{} {place:?}", region_to_string(*r))
            }
            Rvalue::Discriminant(place) => write!(f, "discriminant({place:?})"),
            Rvalue::BinaryOp(bin_op, op1, op2) => write!(f, "{bin_op:?}({op1:?}, {op2:?})"),
            Rvalue::CheckedBinaryOp(bin_op, op1, op2) => {
                write!(f, "Checked{bin_op:?}({op1:?}, {op2:?})")
            }
            Rvalue::UnaryOp(un_op, op) => write!(f, "{un_op:?}({op:?})"),
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
            Rvalue::Aggregate(AggregateKind::Closure(def_id, substs), args) => {
                write!(f, "closure({def_id:?}, {substs:?}, {:?})", args.iter().format(", "))
            }
            Rvalue::Aggregate(AggregateKind::Array(_), args) => {
                write!(f, "[{:?}]", args.iter().format(", "))
            }
            Rvalue::Aggregate(AggregateKind::Tuple, args) => {
                write!(f, "({:?})", args.iter().format(", "))
            }
            Rvalue::Len(place) => write!(f, "Len({place:?})"),
            Rvalue::Cast(kind, op, ty) => write!(f, "{op:?} as {ty:?} [{kind:?}]"),
        }
    }
}

impl fmt::Debug for PointerCast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PointerCast::MutToConstPointer => write!(f, "MutToConstPointer"),
        }
    }
}

impl fmt::Debug for CastKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CastKind::IntToInt => write!(f, "IntToInt"),
            CastKind::FloatToInt => write!(f, "FloatToInt"),
            CastKind::IntToFloat => write!(f, "IntToFloat"),
            CastKind::Pointer(c) => write!(f, "Pointer({c:?})"),
        }
    }
}

impl fmt::Debug for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Copy(place) => write!(f, "copy {place:?}"),
            Self::Move(place) => write!(f, "move {place:?}"),
            Self::Constant(c) => write!(f, "{c:?}"),
        }
    }
}

impl fmt::Debug for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Int(n, int_ty) => write!(f, "{n}{}", int_ty.name_str()),
            Constant::Uint(n, uint_ty) => write!(f, "{n}{}", uint_ty.name_str()),
            Constant::Float(bits, float_ty) => write!(f, "{bits}{}", float_ty.name_str()),
            Constant::Bool(b) => write!(f, "{b}"),
            Constant::Unit => write!(f, "()"),
            Constant::Str => write!(f, "\"<opaque str>\""),
            Constant::Char => write!(f, "\"<opaque char>\""),
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

fn opt_bb_to_str(bb: Option<BasicBlock>) -> String {
    match bb {
        Some(bb) => format!("{bb:?}"),
        None => "None".to_string(),
    }
}
