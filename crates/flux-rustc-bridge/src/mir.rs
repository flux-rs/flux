//! A simplified version of rust mir.

use std::fmt;

use flux_arc_interner::List;
use flux_common::index::{Idx, IndexVec};
use itertools::Itertools;
pub use rustc_abi::{FIRST_VARIANT, FieldIdx, VariantIdx};
use rustc_borrowck::consumers::{BodyWithBorrowckFacts, BorrowData, BorrowIndex};
use rustc_data_structures::{
    fx::FxIndexMap,
    graph::{self, DirectedGraph, StartNode, dominators::Dominators},
    unord::UnordMap,
};
use rustc_hir::def_id::DefId;
use rustc_index::IndexSlice;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::{
    mir::{self, VarDebugInfoContents},
    ty::{FloatTy, IntTy, ParamConst, UintTy},
};
pub use rustc_middle::{
    mir::{
        BasicBlock, BorrowKind, FakeBorrowKind, FakeReadCause, Local, LocalKind, Location,
        RETURN_PLACE, RawPtrKind, START_BLOCK, SourceInfo, SwitchTargets, UnOp, UnwindAction,
    },
    ty::{UserTypeAnnotationIndex, Variance},
};
use rustc_span::{Span, Symbol};

use super::ty::{Const, GenericArg, GenericArgs, Region, Ty};
use crate::{
    def_id_to_string,
    ty::{Binder, FnSig, region_to_string},
};

pub struct Body<'tcx> {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    pub local_decls: IndexVec<Local, LocalDecl>,
    /// During borrow checking, `rustc` generates fresh [region variable ids] for each structurally
    /// different position in a type. For example, given a function
    ///
    /// `fn foo<'a, 'b>(x: &'a S<'a>, y: &'b u32)`
    ///
    /// `rustc` will generate variables `?2` and `?3` for the universal regions `'a` and `'b` (the variable
    /// `?0` correspond to `'static` and `?1` to the implicit lifetime of the function body). Additionally,
    /// it will assign `x` type &'?4 S<'?5>` and `y` type `&'?6 u32` (together with some constraints relating
    /// region variables). Unfortunately, we cannot recover the exact region variables rustc used.
    ///
    /// The exact ids picked for `'a` and `'b` are not too relevant to us, the important part is the regions
    /// used in the types of `x` and `y`. To work around this, we generate fresh regions variables for
    /// the function signature, different from the ones sued by rustc. To recover the correct regions, whenever
    /// there's an assignment of a refinement type `T` to a variable with (unrefined) Rust type `S`, we _match_
    /// both types to infer a region substitution. For this to work, we need to give a different variable id to every
    /// position in `T`. To avoid clashes, we need to use fresh ids, so we start enumerating from the last id
    /// generated by borrow checking.
    ///
    /// To do that, we replicate the [`InferCtxt`] use for mir typeck by generating region variables for every
    /// region in the `RegionInferenceContext`. The [`InferCtxt`] is then used to generate new region variables.
    ///
    /// The ids generated during refinement type checking are purely instrumental and temporary, they should never
    /// appear in a type bound in the environment.
    ///
    /// Besides generating ids when checking a function's body, we also need to generate fresh ids at
    /// function calls.
    ///
    /// Additionally, the [`InferCtxt`] is used during type projection normalization.
    ///
    /// [region variable ids]: super::ty::RegionVid
    /// [`InferCtxt`]: rustc_infer::infer::InferCtxt
    pub infcx: rustc_infer::infer::InferCtxt<'tcx>,
    pub dominator_order_rank: IndexVec<BasicBlock, u32>,
    /// See [`mk_fake_predecessors`]
    fake_predecessors: IndexVec<BasicBlock, usize>,
    body_with_facts: BodyWithBorrowckFacts<'tcx>,
    pub local_names: UnordMap<Local, Symbol>,
}

#[derive(Debug)]
pub struct BasicBlockData<'tcx> {
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator<'tcx>>,
    pub is_cleanup: bool,
}

pub type LocalDecls = IndexSlice<Local, LocalDecl>;

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub ty: Ty,
    pub source_info: SourceInfo,
}

pub struct Terminator<'tcx> {
    pub kind: TerminatorKind<'tcx>,
    pub source_info: SourceInfo,
}

#[derive(Debug)]
pub struct CallArgs<'tcx> {
    pub orig: rustc_middle::ty::GenericArgsRef<'tcx>,
    pub lowered: List<GenericArg>,
}

/// An `Instance` is the resolved call-target at a particular trait-call-site
#[derive(Debug)]
pub struct Instance {
    pub impl_f: DefId,
    pub args: GenericArgs,
}

pub enum CallKind<'tcx> {
    FnDef {
        def_id: DefId,
        generic_args: CallArgs<'tcx>,
        resolved_id: DefId,
        resolved_args: CallArgs<'tcx>,
    },
    FnPtr {
        fn_sig: Binder<FnSig>,
        operand: Operand,
    },
}

#[derive(Debug)]
pub enum TerminatorKind<'tcx> {
    Return,
    Call {
        kind: CallKind<'tcx>,
        args: Vec<Operand>,
        destination: Place,
        target: Option<BasicBlock>,
        unwind: UnwindAction,
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
    Yield {
        value: Operand,
        resume: BasicBlock,
        resume_arg: Place,
        drop: Option<BasicBlock>,
    },
    CoroutineDrop,
    UnwindResume,
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
pub enum NonDivergingIntrinsic {
    Assume(Operand),
}

#[derive(Debug)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    SetDiscriminant(Place, VariantIdx),
    FakeRead(Box<(FakeReadCause, Place)>),
    AscribeUserType(Place, Variance),
    Intrinsic(NonDivergingIntrinsic),
    PlaceMention(Place),
    Nop,
}

/// Corresponds to <https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.Rvalue.html>
pub enum Rvalue {
    Use(Operand),
    Repeat(Operand, Const),
    Ref(Region, BorrowKind, Place),
    RawPtr(RawPtrKind, Place),
    Len(Place),
    Cast(CastKind, Operand, Ty),
    BinaryOp(BinOp, Operand, Operand),
    NullaryOp(NullOp, Ty),
    UnaryOp(UnOp, Operand),
    Discriminant(Place),
    Aggregate(AggregateKind, Vec<Operand>),
    ShallowInitBox(Operand, Ty),
}

#[derive(Copy, Clone)]
pub enum CastKind {
    IntToInt,
    FloatToInt,
    IntToFloat,
    PtrToPtr,
    PointerCoercion(PointerCast),
    PointerExposeProvenance,
    PointerWithExposedProvenance,
}

#[derive(Copy, Clone)]
pub enum PointerCast {
    MutToConstPointer,
    Unsize,
    ClosureFnPointer,
    ReifyFnPointer,
}

#[derive(Debug)]
pub enum AggregateKind {
    Adt(DefId, VariantIdx, GenericArgs, Option<UserTypeAnnotationIndex>, Option<FieldIdx>),
    Array(Ty),
    Tuple,
    Closure(DefId, GenericArgs),
    Coroutine(DefId, GenericArgs),
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
    BitXor,
    Shl,
    Shr,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum NullOp {
    SizeOf,
    AlignOf,
}

pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct Place {
    /// the "root" of the place, e.g. `_1` in `*_1.f.g.h`
    pub local: Local,
    /// path taken to "get" the place e.g. `*.f.g.h` in `*_1.f.g.h` (except also have derefs)
    pub projection: Vec<PlaceElem>,
}

impl Place {
    pub const RETURN: &'static Place = &Place { local: RETURN_PLACE, projection: vec![] };

    pub fn new(local: Local, projection: Vec<PlaceElem>) -> Place {
        Place { local, projection }
    }

    pub fn as_ref(&self) -> PlaceRef<'_> {
        PlaceRef { local: self.local, projection: &self.projection[..] }
    }

    pub fn deref(&self) -> Self {
        let mut projection = self.projection.clone();
        projection.push(PlaceElem::Deref);
        Place { local: self.local, projection }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum PlaceElem {
    Deref,
    Field(FieldIdx),
    Downcast(Option<Symbol>, VariantIdx),
    Index(Local),
    ConstantIndex {
        /// index or -index (in Python terms), depending on from_end
        offset: u64,
        /// The thing being indexed must be at least this long. For arrays this
        /// is always the exact length.
        min_length: u64,
        /// Counting backwards from end? This is always false when indexing an
        /// array.
        from_end: bool,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PlaceRef<'a> {
    pub local: Local,
    pub projection: &'a [PlaceElem],
}

impl<'a> PlaceRef<'a> {
    pub fn truncate(self, i: usize) -> PlaceRef<'a> {
        Self { local: self.local, projection: &self.projection[..i] }
    }

    pub fn to_place(self) -> Place {
        Place { local: self.local, projection: self.projection.to_vec() }
    }

    pub fn last_projection(self) -> Option<(PlaceRef<'a>, PlaceElem)> {
        if let [base @ .., elem] = self.projection {
            Some((PlaceRef { local: self.local, projection: base }, *elem))
        } else {
            None
        }
    }
}

pub enum Constant {
    Int(i128, IntTy),
    Uint(u128, UintTy),
    Float(u128, FloatTy),
    Bool(bool),
    Str(Symbol),
    Char(char),
    Unit,
    Param(ParamConst, Ty),
    /// General catch-all for constants of a given Ty
    Opaque(Ty),
    /// Better than opaque -- we track `DefId` so we can get the actual refinement index
    Unevaluated(Ty, DefId),
}

impl Terminator<'_> {
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
    pub fn new(
        basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
        local_decls: IndexVec<Local, LocalDecl>,
        body_with_facts: BodyWithBorrowckFacts<'tcx>,
        infcx: rustc_infer::infer::InferCtxt<'tcx>,
    ) -> Self {
        let fake_predecessors = mk_fake_predecessors(&basic_blocks);

        // The dominator rank of each node is just its index in a reverse-postorder traversal.
        let graph = &body_with_facts.body.basic_blocks;
        let mut dominator_order_rank = IndexVec::from_elem_n(0, graph.num_nodes());
        let reverse_post_order = graph::iterate::reverse_post_order(graph, graph.start_node());
        assert_eq!(reverse_post_order.len(), graph.num_nodes());
        for (rank, bb) in (0u32..).zip(reverse_post_order) {
            dominator_order_rank[bb] = rank;
        }
        let local_names = body_with_facts
            .body
            .var_debug_info
            .iter()
            .flat_map(|var_debug_info| {
                if let VarDebugInfoContents::Place(place) = var_debug_info.value {
                    let local = place.as_local()?;
                    Some((local, var_debug_info.name))
                } else {
                    None
                }
            })
            .collect();
        Self {
            basic_blocks,
            local_decls,
            infcx,
            fake_predecessors,
            body_with_facts,
            dominator_order_rank,
            local_names,
        }
    }

    pub fn def_id(&self) -> DefId {
        self.inner().source.def_id()
    }

    pub fn span(&self) -> Span {
        self.body_with_facts.body.span
    }

    pub fn inner(&self) -> &mir::Body<'tcx> {
        &self.body_with_facts.body
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
    pub fn is_join_point(&self, bb: BasicBlock) -> bool {
        let total_preds = self.body_with_facts.body.basic_blocks.predecessors()[bb].len();
        let real_preds = total_preds - self.fake_predecessors[bb];
        // The entry block is a joint point if it has at least one predecessor because there's
        // an implicit goto from the environment at the beginning of the function.
        real_preds > usize::from(bb != START_BLOCK)
    }

    #[inline]
    pub fn dominators(&self) -> &Dominators<BasicBlock> {
        self.body_with_facts.body.basic_blocks.dominators()
    }

    pub fn terminator_loc(&self, bb: BasicBlock) -> Location {
        Location { block: bb, statement_index: self.basic_blocks[bb].statements.len() }
    }

    pub fn calculate_borrows_out_of_scope_at_location(
        &self,
    ) -> FxIndexMap<Location, Vec<BorrowIndex>> {
        rustc_borrowck::consumers::calculate_borrows_out_of_scope_at_location(
            &self.body_with_facts.body,
            &self.body_with_facts.region_inference_context,
            &self.body_with_facts.borrow_set,
        )
    }

    pub fn borrow_data(&self, idx: BorrowIndex) -> &BorrowData<'tcx> {
        self.body_with_facts
            .borrow_set
            .location_map()
            .get_index(idx.as_usize())
            .unwrap()
            .1
    }

    pub fn rustc_body(&self) -> &mir::Body<'tcx> {
        &self.body_with_facts.body
    }

    pub fn local_kind(&self, local: Local) -> LocalKind {
        self.body_with_facts.body.local_kind(local)
    }
}

/// The `FalseEdge/imaginary_target` edges mess up the `is_join_point` computation which creates spurious
/// join points that lose information e.g. in match arms, the k+1-th arm has the k-th arm as a "fake"
/// predecessor so we lose the assumptions specific to the k+1-th arm due to a spurious join. This code
/// corrects for this problem by computing the number of "fake" predecessors and decreasing them from
/// the total number of "predecessors" returned by `rustc`.  The option is to recompute "predecessors"
/// from scratch but we may miss some cases there. (see also [`is_join_point`])
///
/// [`is_join_point`]: crate::mir::Body::is_join_point
fn mk_fake_predecessors(
    basic_blocks: &IndexVec<BasicBlock, BasicBlockData>,
) -> IndexVec<BasicBlock, usize> {
    let mut res: IndexVec<BasicBlock, usize> = basic_blocks.iter().map(|_| 0).collect();

    for bb in basic_blocks {
        if let Some(terminator) = &bb.terminator
            && let TerminatorKind::FalseEdge { imaginary_target, .. } = terminator.kind
        {
            res[imaginary_target] += 1;
        }
    }
    res
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
            StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op)) => {
                write!(f, "Assume({op:?})")
            }
        }
    }
}

impl fmt::Debug for CallKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CallKind::FnDef { resolved_id, resolved_args, .. } => {
                let fname = rustc_middle::ty::tls::with(|tcx| {
                    let path = tcx.def_path(*resolved_id);
                    path.data.iter().join("::")
                });
                write!(f, "call {fname}")?;
                if !resolved_args.lowered.is_empty() {
                    write!(f, "<{:?}>", resolved_args.lowered.iter().format(", "))?;
                }
                Ok(())
            }
            CallKind::FnPtr { fn_sig, operand } => write!(f, "FnPtr[{operand:?}]({fn_sig:?})"),
        }
    }
}

impl fmt::Debug for Terminator<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TerminatorKind::Return => write!(f, "return"),
            TerminatorKind::Unreachable => write!(f, "unreachable"),
            TerminatorKind::Call { kind, args, destination, target, unwind, .. } => {
                write!(
                    f,
                    "{destination:?} = call {kind:?}({args:?}) -> [return: {target}, unwind: {unwind:?}]",
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
            TerminatorKind::UnwindResume => write!(f, "resume"),
            TerminatorKind::CoroutineDrop => write!(f, "generator_drop"),
            TerminatorKind::Yield { value, resume, drop, resume_arg } => {
                write!(
                    f,
                    "{resume_arg:?} = yield({value:?}) -> [resume: {resume:?}, drop: {drop:?}]"
                )
            }
        }
    }
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_ref())
    }
}

impl fmt::Debug for PlaceRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut p = format!("{:?}", self.local);
        let mut need_parens = false;
        for elem in self.projection {
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
                PlaceElem::ConstantIndex { offset, min_length, .. } => {
                    p = format!("{p}[{offset:?} of {min_length:?}]");
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
            Rvalue::Ref(r, BorrowKind::Fake(FakeBorrowKind::Shallow), place) => {
                write!(f, "&{} fake shallow {place:?}", region_to_string(*r))
            }
            Rvalue::Ref(r, BorrowKind::Fake(FakeBorrowKind::Deep), place) => {
                write!(f, "&{} fake deep {place:?}", region_to_string(*r))
            }
            Rvalue::RawPtr(mutbl, place) => write!(f, "&raw {} {place:?}", mutbl.ptr_str()),
            Rvalue::Discriminant(place) => write!(f, "discriminant({place:?})"),
            Rvalue::BinaryOp(bin_op, op1, op2) => write!(f, "{bin_op:?}({op1:?}, {op2:?})"),
            Rvalue::NullaryOp(null_op, ty) => write!(f, "{null_op:?}({ty:?})"),
            Rvalue::UnaryOp(un_op, op) => write!(f, "{un_op:?}({op:?})"),
            Rvalue::Aggregate(AggregateKind::Adt(def_id, variant_idx, args, _, _), operands) => {
                let (fname, variant_name) = rustc_middle::ty::tls::with(|tcx| {
                    let variant_name = tcx.adt_def(*def_id).variant(*variant_idx).name;
                    let fname = tcx.def_path(*def_id).data.iter().join("::");
                    (fname, variant_name)
                });
                write!(f, "{fname}::{variant_name}")?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "),)?;
                }
                if !operands.is_empty() {
                    write!(f, "({:?})", operands.iter().format(", "))?;
                }
                Ok(())
            }
            Rvalue::Aggregate(AggregateKind::Closure(def_id, args), operands) => {
                write!(
                    f,
                    "closure({}, {args:?}, {:?})",
                    def_id_to_string(*def_id),
                    operands.iter().format(", ")
                )
            }
            Rvalue::Aggregate(AggregateKind::Coroutine(def_id, args), operands) => {
                write!(
                    f,
                    "generator({}, {args:?}, {:?})",
                    def_id_to_string(*def_id),
                    operands.iter().format(", ")
                )
            }
            Rvalue::Aggregate(AggregateKind::Array(_), args) => {
                write!(f, "[{:?}]", args.iter().format(", "))
            }
            Rvalue::Aggregate(AggregateKind::Tuple, args) => {
                write!(f, "({:?})", args.iter().format(", "))
            }
            Rvalue::Len(place) => write!(f, "Len({place:?})"),
            Rvalue::Cast(kind, op, ty) => write!(f, "{op:?} as {ty:?} [{kind:?}]"),
            Rvalue::Repeat(op, c) => write!(f, "[{op:?}; {c:?}]"),
            Rvalue::ShallowInitBox(op, ty) => write!(f, "ShallowInitBox({op:?}, {ty:?})"),
        }
    }
}

impl fmt::Debug for PointerCast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PointerCast::MutToConstPointer => write!(f, "MutToConstPointer"),
            PointerCast::Unsize => write!(f, "Unsize"),
            PointerCast::ClosureFnPointer => write!(f, "ClosureFnPointer"),
            PointerCast::ReifyFnPointer => write!(f, "ReifyFnPointer"),
        }
    }
}

impl fmt::Debug for CastKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CastKind::IntToInt => write!(f, "IntToInt"),
            CastKind::FloatToInt => write!(f, "FloatToInt"),
            CastKind::IntToFloat => write!(f, "IntToFloat"),
            CastKind::PtrToPtr => write!(f, "PtrToPtr"),
            CastKind::PointerCoercion(c) => write!(f, "Pointer({c:?})"),
            CastKind::PointerExposeProvenance => write!(f, "PointerExposeProvenance"),
            CastKind::PointerWithExposedProvenance => write!(f, "PointerWithExposedProvenance"),
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
            Constant::Str(s) => write!(f, "\"{s:?}\""),
            Constant::Char(c) => write!(f, "\'{c}\'"),
            Constant::Opaque(ty) => write!(f, "<opaque {ty:?}>"),
            Constant::Param(p, _) => write!(f, "{p:?}"),
            Constant::Unevaluated(ty, def_id) => write!(f, "<uneval {ty:?} from {def_id:?}>"),
        }
    }
}

fn opt_bb_to_str(bb: Option<BasicBlock>) -> String {
    match bb {
        Some(bb) => format!("{bb:?}"),
        None => "None".to_string(),
    }
}
