//! A simplified version of rust types.

mod subst;

use std::fmt;

pub use flux_arc_interner::List;
use flux_arc_interner::{Interned, impl_internable, impl_slice_internable};
use flux_common::{bug, tracked_span_assert_eq, tracked_span_bug};
use itertools::Itertools;
use rustc_abi;
pub use rustc_abi::{FIRST_VARIANT, FieldIdx, VariantIdx};
use rustc_hir::{Safety, def_id::DefId};
use rustc_index::{IndexSlice, IndexVec};
use rustc_macros::{TyDecodable, TyEncodable, extension};
pub use rustc_middle::{
    mir::Mutability,
    ty::{
        BoundRegionKind, BoundVar, ConstVid, DebruijnIndex, EarlyParamRegion, FloatTy, IntTy,
        LateParamRegion, LateParamRegionKind, ParamTy, RegionVid, ScalarInt, UintTy,
    },
};
use rustc_middle::{
    mir::Promoted,
    ty::{self as rustc_ty, AdtFlags, ParamConst, TyCtxt},
};
use rustc_span::Symbol;
pub use rustc_type_ir::InferConst;

use self::subst::Subst;
use super::ToRustc;
use crate::def_id_to_string;

#[derive(Debug, Clone)]
pub struct Generics<'tcx> {
    pub params: List<GenericParamDef>,
    pub orig: &'tcx rustc_middle::ty::Generics,
}

#[derive(Clone)]
pub struct EarlyBinder<T>(pub T);

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct Binder<T>(T, List<BoundVariableKind>);

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub enum BoundVariableKind {
    Region(BoundRegionKind),
}

impl BoundVariableKind {
    // We can't implement [`ToRustc`] on [`List<BoundVariableKind>`] because of coherence so we add
    // it here
    fn to_rustc<'tcx>(
        vars: &[Self],
        tcx: TyCtxt<'tcx>,
    ) -> &'tcx rustc_middle::ty::List<rustc_middle::ty::BoundVariableKind> {
        tcx.mk_bound_variable_kinds_from_iter(vars.iter().flat_map(|kind| {
            match kind {
                BoundVariableKind::Region(brk) => {
                    Some(rustc_middle::ty::BoundVariableKind::Region(*brk))
                }
            }
        }))
    }
}

#[derive(Debug, Hash, Eq, PartialEq, TyEncodable, TyDecodable)]
pub struct GenericParamDef {
    pub def_id: DefId,
    pub index: u32,
    pub name: Symbol,
    pub kind: GenericParamDefKind,
}

#[derive(Debug, Hash, Eq, PartialEq, Clone, Copy, TyEncodable, TyDecodable)]
pub enum GenericParamDefKind {
    Type { has_default: bool },
    Lifetime,
    Const { has_default: bool },
}

#[derive(Clone, Debug)]
pub struct GenericPredicates {
    pub parent: Option<DefId>,
    pub predicates: List<Clause>,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct Clause {
    pub kind: Binder<ClauseKind>,
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub enum ClauseKind {
    Trait(TraitPredicate),
    Projection(ProjectionPredicate),
    RegionOutlives(RegionOutlivesPredicate),
    TypeOutlives(TypeOutlivesPredicate),
    ConstArgHasType(Const, Ty),
}

#[derive(Eq, PartialEq, Hash, Clone, Debug, TyEncodable, TyDecodable)]
pub struct OutlivesPredicate<T>(pub T, pub Region);

pub type TypeOutlivesPredicate = OutlivesPredicate<Ty>;
pub type RegionOutlivesPredicate = OutlivesPredicate<Region>;

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
}

#[derive(PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub struct TraitRef {
    pub def_id: DefId,
    pub args: GenericArgs,
}

impl TraitRef {
    pub fn self_ty(&self) -> &Ty {
        self.args[0].expect_type()
    }
}

pub type PolyTraitRef = Binder<TraitRef>;

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct ProjectionPredicate {
    pub projection_ty: AliasTy,
    pub term: Ty,
}
#[derive(Clone, Hash, PartialEq, Eq, TyEncodable, TyDecodable)]
pub struct FnSig {
    pub safety: Safety,
    pub abi: rustc_abi::ExternAbi,
    pub(crate) inputs_and_output: List<Ty>,
}

pub type PolyFnSig = Binder<FnSig>;

impl PolyFnSig {
    pub fn unpack_closure_sig(&self) -> Self {
        let vars = self.vars().clone();
        let fn_sig = self.skip_binder_ref();
        let [input] = &fn_sig.inputs() else {
            bug!("closure signature should have at least two values");
        };
        let fn_sig = FnSig {
            safety: fn_sig.safety,
            abi: fn_sig.abi,
            inputs_and_output: input
                .tuple_fields()
                .iter()
                .cloned()
                .chain([fn_sig.output().clone()])
                .collect(),
        };
        Binder::bind_with_vars(fn_sig, vars)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct Ty(Interned<TyS>);

#[derive(Debug, Eq, PartialEq, Hash, Clone, TyEncodable, TyDecodable)]
pub struct AdtDef(Interned<AdtDefData>);

#[derive(Debug, TyEncodable, TyDecodable)]
pub struct AdtDefData {
    pub did: DefId,
    variants: IndexVec<VariantIdx, VariantDef>,
    discrs: IndexVec<VariantIdx, u128>,
    flags: AdtFlags,
}

/// There should be only one AdtDef for each `did`, therefore
/// it is fine to implement `Hash` only based on `did`.
impl std::hash::Hash for AdtDefData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.did.hash(state);
    }
}

/// There should be only one AdtDef for each `did`, therefore
/// it is fine to implement `PartialEq` only based on `did`.
impl PartialEq for AdtDefData {
    fn eq(&self, other: &Self) -> bool {
        self.did == other.did
    }
}

impl Eq for AdtDefData {}

#[derive(Debug, TyEncodable, TyDecodable)]
pub struct VariantDef {
    pub def_id: DefId,
    pub name: Symbol,
    pub fields: IndexVec<FieldIdx, FieldDef>,
}

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct FieldDef {
    pub did: DefId,
    pub name: Symbol,
}

#[derive(Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
struct TyS {
    kind: TyKind,
}

#[derive(Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum TyKind {
    Adt(AdtDef, GenericArgs),
    Array(Ty, Const),
    Bool,
    Str,
    Char,
    Float(FloatTy),
    Int(IntTy),
    Never,
    Param(ParamTy),
    Ref(Region, Ty, Mutability),
    Tuple(List<Ty>),
    Uint(UintTy),
    Slice(Ty),
    FnPtr(PolyFnSig),
    FnDef(DefId, GenericArgs),
    Closure(DefId, GenericArgs),
    Coroutine(DefId, GenericArgs),
    CoroutineWitness(DefId, GenericArgs),
    Alias(AliasKind, AliasTy),
    RawPtr(Ty, Mutability),
    Dynamic(List<Binder<ExistentialPredicate>>, Region),
    Foreign(DefId),
}

#[derive(PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum ExistentialPredicate {
    Trait(ExistentialTraitRef),
    Projection(ExistentialProjection),
    AutoTrait(DefId),
}

pub type PolyExistentialPredicate = Binder<ExistentialPredicate>;

#[derive(PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct ExistentialTraitRef {
    pub def_id: DefId,
    pub args: GenericArgs,
}

#[derive(PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct ExistentialProjection {
    pub def_id: DefId,
    pub args: GenericArgs,
    pub term: Ty,
}

#[derive(Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct AliasTy {
    pub args: GenericArgs,
    pub def_id: DefId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum AliasKind {
    Projection,
    Opaque,
    Free,
}

impl<'tcx> ToRustc<'tcx> for AliasKind {
    type T = rustc_middle::ty::AliasTyKind;

    fn to_rustc(&self, _tcx: TyCtxt<'tcx>) -> Self::T {
        use rustc_middle::ty;
        match self {
            AliasKind::Opaque => ty::AliasTyKind::Opaque,
            AliasKind::Projection => ty::AliasTyKind::Projection,
            AliasKind::Free => ty::AliasTyKind::Free,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct Const {
    pub kind: ConstKind,
}

impl<'tcx> ToRustc<'tcx> for UnevaluatedConst {
    type T = rustc_middle::ty::UnevaluatedConst<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        let args = tcx.mk_args_from_iter(self.args.iter().map(|arg| arg.to_rustc(tcx)));
        rustc_ty::UnevaluatedConst::new(self.def, args)
    }
}

impl Const {
    pub fn from_usize(tcx: TyCtxt, v: usize) -> Self {
        Self {
            kind: ConstKind::Value(
                Ty::mk_uint(UintTy::Usize),
                ValTree::Leaf(ScalarInt::try_from_target_usize(v as u128, tcx).unwrap()),
            ),
        }
    }
}

impl<'tcx> ToRustc<'tcx> for ValTree {
    type T = rustc_middle::ty::ValTree<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        match self {
            ValTree::Leaf(scalar) => rustc_middle::ty::ValTree::from_scalar_int(tcx, *scalar),
            ValTree::Branch(trees) => {
                let trees = trees.iter().map(|tree| tree.to_rustc(tcx));
                rustc_middle::ty::ValTree::from_branches(tcx, trees)
            }
        }
    }
}

impl<'tcx> ToRustc<'tcx> for Const {
    type T = rustc_ty::Const<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        let kind = match &self.kind {
            ConstKind::Param(param_const) => rustc_ty::ConstKind::Param(*param_const),
            ConstKind::Value(ty, val) => {
                let val = rustc_ty::Value { ty: ty.to_rustc(tcx), valtree: val.to_rustc(tcx) };
                rustc_ty::ConstKind::Value(val)
            }
            ConstKind::Infer(infer_const) => rustc_ty::ConstKind::Infer(*infer_const),
            ConstKind::Unevaluated(uneval_const) => {
                rustc_ty::ConstKind::Unevaluated(uneval_const.to_rustc(tcx))
            }
        };
        rustc_ty::Const::new(tcx, kind)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct UnevaluatedConst {
    pub def: DefId,
    pub args: GenericArgs,
    pub promoted: Option<Promoted>,
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum ValTree {
    Leaf(ScalarInt),
    Branch(List<ValTree>),
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum ConstKind {
    Param(ParamConst),
    Value(Ty, ValTree),
    Infer(InferConst),
    Unevaluated(UnevaluatedConst),
}

#[derive(PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum GenericArg {
    Ty(Ty),
    Lifetime(Region),
    Const(Const),
}

pub type GenericArgs = List<GenericArg>;

#[extension(pub trait GenericArgsExt)]
impl GenericArgs {
    fn box_args(&self) -> (&Ty, &Ty) {
        if let [GenericArg::Ty(deref), GenericArg::Ty(alloc)] = &self[..] {
            (deref, alloc)
        } else {
            bug!("invalid generic arguments for box");
        }
    }

    fn as_closure(&self) -> ClosureArgs {
        ClosureArgs { args: self.clone() }
    }

    fn as_coroutine(&self) -> CoroutineArgs {
        CoroutineArgs { args: self.clone() }
    }
}

pub struct CoroutineArgs {
    pub args: GenericArgs,
}

pub struct ClosureArgs {
    pub args: GenericArgs,
}

#[expect(unused, reason = "keeping this in case we use it")]
pub struct ClosureArgsParts<'a, T> {
    parent_args: &'a [T],
    closure_kind_ty: &'a T,
    closure_sig_as_fn_ptr_ty: &'a T,
    tupled_upvars_ty: &'a T,
}

#[derive(Debug)]
pub struct CoroutineArgsParts<'a> {
    pub parent_args: &'a [GenericArg],
    pub kind_ty: &'a Ty,
    pub resume_ty: &'a Ty,
    pub yield_ty: &'a Ty,
    pub return_ty: &'a Ty,
    pub tupled_upvars_ty: &'a Ty,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum Region {
    ReBound(DebruijnIndex, BoundRegion),
    ReEarlyParam(EarlyParamRegion),
    ReStatic,
    ReVar(RegionVid),
    ReLateParam(LateParamRegion),
    ReErased,
}

impl<'tcx> ToRustc<'tcx> for Region {
    type T = rustc_middle::ty::Region<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        match *self {
            Region::ReBound(debruijn, bound_region) => {
                rustc_middle::ty::Region::new_bound(tcx, debruijn, bound_region.to_rustc(tcx))
            }
            Region::ReEarlyParam(epr) => rustc_middle::ty::Region::new_early_param(tcx, epr),
            Region::ReStatic => tcx.lifetimes.re_static,
            Region::ReVar(rvid) => rustc_middle::ty::Region::new_var(tcx, rvid),
            Region::ReLateParam(LateParamRegion { scope, kind }) => {
                rustc_middle::ty::Region::new_late_param(tcx, scope, kind)
            }
            Region::ReErased => tcx.lifetimes.re_erased,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub struct BoundRegion {
    pub var: BoundVar,
    pub kind: BoundRegionKind,
}

impl<'tcx> ToRustc<'tcx> for BoundRegion {
    type T = rustc_middle::ty::BoundRegion;

    fn to_rustc(&self, _tcx: TyCtxt<'tcx>) -> Self::T {
        rustc_middle::ty::BoundRegion { var: self.var, kind: self.kind }
    }
}

impl Generics<'_> {
    pub fn parent(&self) -> Option<DefId> {
        self.orig.parent
    }

    pub fn parent_count(&self) -> usize {
        self.orig.parent_count
    }
}

impl Clause {
    pub(crate) fn new(kind: Binder<ClauseKind>) -> Clause {
        Clause { kind }
    }
}

impl<T> EarlyBinder<T> {
    pub fn skip_binder(self) -> T {
        self.0
    }

    pub fn instantiate_identity(self) -> T {
        self.0
    }
}

impl EarlyBinder<Ty> {
    pub fn subst(&self, args: &[GenericArg]) -> Ty {
        self.0.subst(args)
    }
}

impl<T> Binder<T> {
    pub fn dummy(value: T) -> Binder<T> {
        Binder(value, List::empty())
    }

    pub fn bind_with_vars(value: T, vars: impl Into<List<BoundVariableKind>>) -> Binder<T> {
        Binder(value, vars.into())
    }

    pub fn skip_binder(self) -> T {
        self.0
    }

    pub fn skip_binder_ref(&self) -> &T {
        self.as_ref().skip_binder()
    }

    pub fn as_ref(&self) -> Binder<&T> {
        Binder(&self.0, self.1.clone())
    }

    pub fn vars(&self) -> &List<BoundVariableKind> {
        &self.1
    }
}

impl FnSig {
    pub fn inputs(&self) -> &[Ty] {
        &self.inputs_and_output[..self.inputs_and_output.len() - 1]
    }

    pub fn output(&self) -> &Ty {
        &self.inputs_and_output[self.inputs_and_output.len() - 1]
    }
}

impl GenericArg {
    pub fn expect_type(&self) -> &Ty {
        if let GenericArg::Ty(ty) = self {
            ty
        } else {
            bug!("expected `GenericArg::Ty`, found {:?}", self)
        }
    }

    fn expect_lifetime(&self) -> Region {
        if let GenericArg::Lifetime(re) = self {
            *re
        } else {
            bug!("expected `GenericArg::Lifetime`, found {:?}", self)
        }
    }

    fn expect_const(&self) -> &Const {
        if let GenericArg::Const(c) = self {
            c
        } else {
            bug!("expected `GenericArg::Const`, found {:?}", self)
        }
    }
}

impl<'tcx> ToRustc<'tcx> for GenericArgs {
    type T = rustc_middle::ty::GenericArgsRef<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        tcx.mk_args_from_iter(self.iter().map(|arg| arg.to_rustc(tcx)))
    }
}

impl<'tcx> ToRustc<'tcx> for GenericArg {
    type T = rustc_middle::ty::GenericArg<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        use rustc_middle::ty;
        match self {
            GenericArg::Ty(ty) => ty::GenericArg::from(ty.to_rustc(tcx)),
            GenericArg::Lifetime(re) => ty::GenericArg::from(re.to_rustc(tcx)),
            GenericArg::Const(c) => ty::GenericArg::from(c.to_rustc(tcx)),
        }
    }
}

impl CoroutineArgs {
    pub fn tupled_upvars_ty(&self) -> &Ty {
        self.split().tupled_upvars_ty
    }

    pub fn upvar_tys(&self) -> impl Iterator<Item = &Ty> {
        self.tupled_upvars_ty().tuple_fields().iter()
    }

    pub fn resume_ty(&self) -> &Ty {
        self.split().resume_ty
    }

    fn split(&self) -> CoroutineArgsParts<'_> {
        match &self.args[..] {
            [parent_args @ .., kind_ty, resume_ty, yield_ty, return_ty, tupled_upvars_ty] => {
                CoroutineArgsParts {
                    parent_args,
                    kind_ty: kind_ty.expect_type(),
                    resume_ty: resume_ty.expect_type(),
                    yield_ty: yield_ty.expect_type(),
                    return_ty: return_ty.expect_type(),
                    tupled_upvars_ty: tupled_upvars_ty.expect_type(),
                }
            }
            _ => bug!("generator args missing synthetics"),
        }
    }
}

impl ClosureArgs {
    pub fn tupled_upvars_ty(&self) -> &Ty {
        self.split().tupled_upvars_ty.expect_type()
    }

    pub fn upvar_tys(&self) -> &List<Ty> {
        self.tupled_upvars_ty().tuple_fields()
    }

    pub fn split(&self) -> ClosureArgsParts<'_, GenericArg> {
        match &self.args[..] {
            [parent_args @ .., closure_kind_ty, closure_sig_as_fn_ptr_ty, tupled_upvars_ty] => {
                ClosureArgsParts {
                    parent_args,
                    closure_kind_ty,
                    closure_sig_as_fn_ptr_ty,
                    tupled_upvars_ty,
                }
            }
            _ => bug!("closure args missing synthetics"),
        }
    }

    pub fn sig_as_fn_ptr_ty(&self) -> &Ty {
        self.split().closure_sig_as_fn_ptr_ty.expect_type()
    }

    pub fn kind_ty(&self) -> &Ty {
        self.split().closure_kind_ty.expect_type()
    }
}

impl AdtDef {
    pub(crate) fn new(data: AdtDefData) -> Self {
        Self(Interned::new(data))
    }

    pub fn did(&self) -> DefId {
        self.0.did
    }

    pub fn flags(&self) -> AdtFlags {
        self.0.flags
    }

    pub fn is_struct(&self) -> bool {
        self.flags().contains(AdtFlags::IS_STRUCT)
    }

    pub fn is_union(&self) -> bool {
        self.flags().contains(AdtFlags::IS_UNION)
    }

    pub fn is_enum(&self) -> bool {
        self.flags().contains(AdtFlags::IS_ENUM)
    }

    pub fn is_box(&self) -> bool {
        self.flags().contains(AdtFlags::IS_BOX)
    }

    pub fn variant(&self, idx: VariantIdx) -> &VariantDef {
        &self.0.variants[idx]
    }

    pub fn variants(&self) -> &IndexSlice<VariantIdx, VariantDef> {
        &self.0.variants
    }

    pub fn discriminants(&self) -> impl Iterator<Item = (VariantIdx, u128)> + '_ {
        self.0
            .discrs
            .iter_enumerated()
            .map(|(idx, discr)| (idx, *discr))
    }

    pub fn non_enum_variant(&self) -> &VariantDef {
        assert!(self.is_struct() || self.is_union());
        self.variant(FIRST_VARIANT)
    }
}

impl<'tcx> ToRustc<'tcx> for AdtDef {
    type T = rustc_middle::ty::AdtDef<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        tcx.adt_def(self.did())
    }
}

impl AdtDefData {
    pub(crate) fn new<'tcx>(
        tcx: TyCtxt<'tcx>,
        adt_def: rustc_middle::ty::AdtDef<'tcx>,
        variants: IndexVec<VariantIdx, VariantDef>,
    ) -> Self {
        let discrs: IndexVec<VariantIdx, u128> = if adt_def.is_enum() {
            adt_def
                .discriminants(tcx)
                .map(|(_, discr)| discr.val)
                .collect()
        } else {
            IndexVec::from_raw(vec![0])
        };
        tracked_span_assert_eq!(discrs.len(), variants.len());
        Self { did: adt_def.did(), variants, flags: adt_def.flags(), discrs }
    }
}

impl AliasTy {
    /// This method work only with associated type projections (i.e., no opaque tpes)
    pub fn self_ty(&self) -> &Ty {
        self.args[0].expect_type()
    }
}

impl TyKind {
    fn intern(self) -> Ty {
        Ty(Interned::new(TyS { kind: self }))
    }
}

impl Ty {
    pub fn mk_adt(adt_def: AdtDef, args: impl Into<GenericArgs>) -> Ty {
        let args = args.into();
        TyKind::Adt(adt_def, args).intern()
    }

    pub fn mk_closure(def_id: DefId, args: impl Into<GenericArgs>) -> Ty {
        TyKind::Closure(def_id, args.into()).intern()
    }

    pub fn mk_fn_def(def_id: DefId, args: impl Into<GenericArgs>) -> Ty {
        TyKind::FnDef(def_id, args.into()).intern()
    }

    pub fn mk_coroutine(def_id: DefId, args: impl Into<GenericArgs>) -> Ty {
        TyKind::Coroutine(def_id, args.into()).intern()
    }

    pub fn mk_generator_witness(def_id: DefId, args: GenericArgs) -> Ty {
        TyKind::CoroutineWitness(def_id, args).intern()
    }

    pub fn mk_alias(kind: AliasKind, def_id: DefId, args: impl Into<GenericArgs>) -> Ty {
        let alias_ty = AliasTy { args: args.into(), def_id };
        TyKind::Alias(kind, alias_ty).intern()
    }

    pub fn mk_array(ty: Ty, c: Const) -> Ty {
        TyKind::Array(ty, c).intern()
    }

    pub fn mk_slice(ty: Ty) -> Ty {
        TyKind::Slice(ty).intern()
    }

    pub fn mk_fn_ptr(fn_sig: PolyFnSig) -> Ty {
        TyKind::FnPtr(fn_sig).intern()
    }

    pub fn mk_raw_ptr(ty: Ty, mutbl: Mutability) -> Ty {
        TyKind::RawPtr(ty, mutbl).intern()
    }

    pub fn mk_bool() -> Ty {
        TyKind::Bool.intern()
    }

    pub fn mk_float(float_ty: FloatTy) -> Ty {
        TyKind::Float(float_ty).intern()
    }

    pub fn mk_int(int_ty: IntTy) -> Ty {
        TyKind::Int(int_ty).intern()
    }

    pub fn mk_never() -> Ty {
        TyKind::Never.intern()
    }

    pub fn mk_param(param: ParamTy) -> Ty {
        TyKind::Param(param).intern()
    }

    pub fn mk_dynamic(exi_preds: impl Into<List<Binder<ExistentialPredicate>>>, r: Region) -> Ty {
        TyKind::Dynamic(exi_preds.into(), r).intern()
    }

    pub fn mk_ref(region: Region, ty: Ty, mutability: Mutability) -> Ty {
        TyKind::Ref(region, ty, mutability).intern()
    }

    pub fn mk_tuple(tys: impl Into<List<Ty>>) -> Ty {
        TyKind::Tuple(tys.into()).intern()
    }

    pub fn mk_uint(uint_ty: UintTy) -> Ty {
        TyKind::Uint(uint_ty).intern()
    }

    pub fn mk_str() -> Ty {
        TyKind::Str.intern()
    }

    pub fn mk_char() -> Ty {
        TyKind::Char.intern()
    }

    pub fn mk_foreign(def_id: DefId) -> Ty {
        TyKind::Foreign(def_id).intern()
    }

    pub fn deref(&self) -> Ty {
        match self.kind() {
            TyKind::Adt(adt_def, args) if adt_def.is_box() => args[0].expect_type().clone(),
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => ty.clone(),
            _ => tracked_span_bug!("deref projection of non-dereferenceable ty `{self:?}`"),
        }
    }

    pub fn kind(&self) -> &TyKind {
        &self.0.kind
    }

    pub fn tuple_fields(&self) -> &List<Ty> {
        match self.kind() {
            TyKind::Tuple(tys) => tys,
            _ => bug!("tuple_fields called on non-tuple"),
        }
    }

    pub fn expect_adt(&self) -> (&AdtDef, &GenericArgs) {
        match self.kind() {
            TyKind::Adt(adt_def, args) => (adt_def, args),
            _ => bug!("expect_adt called on non-adt"),
        }
    }

    pub fn is_mut_ref(&self) -> bool {
        matches!(self.kind(), TyKind::Ref(.., Mutability::Mut))
    }

    pub fn is_box(&self) -> bool {
        matches!(self.kind(), TyKind::Adt(adt, ..) if adt.is_box())
    }
}

impl<'tcx, V> ToRustc<'tcx> for Binder<V>
where
    V: ToRustc<'tcx, T: rustc_middle::ty::TypeVisitable<TyCtxt<'tcx>>>,
{
    type T = rustc_middle::ty::Binder<'tcx, V::T>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        let vars = BoundVariableKind::to_rustc(self.vars(), tcx);
        let value = self.skip_binder_ref().to_rustc(tcx);
        rustc_middle::ty::Binder::bind_with_vars(value, vars)
    }
}

impl<'tcx> ToRustc<'tcx> for FnSig {
    type T = rustc_middle::ty::FnSig<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        tcx.mk_fn_sig(
            self.inputs().iter().map(|ty| ty.to_rustc(tcx)),
            self.output().to_rustc(tcx),
            false,
            self.safety,
            self.abi,
        )
    }
}

impl<'tcx> ToRustc<'tcx> for AliasTy {
    type T = rustc_middle::ty::AliasTy<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        rustc_middle::ty::AliasTy::new(tcx, self.def_id, self.args.to_rustc(tcx))
    }
}

impl<'tcx> ToRustc<'tcx> for ExistentialPredicate {
    type T = rustc_middle::ty::ExistentialPredicate<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        match self {
            ExistentialPredicate::Trait(trait_ref) => {
                let trait_ref = rustc_middle::ty::ExistentialTraitRef::new_from_args(
                    tcx,
                    trait_ref.def_id,
                    trait_ref.args.to_rustc(tcx),
                );
                rustc_middle::ty::ExistentialPredicate::Trait(trait_ref)
            }
            ExistentialPredicate::Projection(projection) => {
                rustc_middle::ty::ExistentialPredicate::Projection(
                    rustc_middle::ty::ExistentialProjection::new_from_args(
                        tcx,
                        projection.def_id,
                        projection.args.to_rustc(tcx),
                        projection.term.to_rustc(tcx).into(),
                    ),
                )
            }
            ExistentialPredicate::AutoTrait(def_id) => {
                rustc_middle::ty::ExistentialPredicate::AutoTrait(*def_id)
            }
        }
    }
}

impl<'tcx> ToRustc<'tcx> for Ty {
    type T = rustc_middle::ty::Ty<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> rustc_middle::ty::Ty<'tcx> {
        match self.kind() {
            TyKind::Bool => tcx.types.bool,
            TyKind::Str => tcx.types.str_,
            TyKind::Char => tcx.types.char,
            TyKind::Never => tcx.types.never,
            TyKind::Foreign(def_id) => rustc_ty::Ty::new_foreign(tcx, *def_id),
            TyKind::Float(float_ty) => rustc_ty::Ty::new_float(tcx, *float_ty),
            TyKind::Int(int_ty) => rustc_ty::Ty::new_int(tcx, *int_ty),
            TyKind::Uint(uint_ty) => rustc_ty::Ty::new_uint(tcx, *uint_ty),
            TyKind::Adt(adt_def, args) => {
                let adt_def = adt_def.to_rustc(tcx);
                let args = tcx.mk_args_from_iter(args.iter().map(|arg| arg.to_rustc(tcx)));
                rustc_ty::Ty::new_adt(tcx, adt_def, args)
            }
            TyKind::FnDef(def_id, args) => {
                let args = tcx.mk_args_from_iter(args.iter().map(|arg| arg.to_rustc(tcx)));
                rustc_ty::Ty::new_fn_def(tcx, *def_id, args)
            }
            TyKind::Array(ty, len) => {
                let ty = ty.to_rustc(tcx);
                let len = len.to_rustc(tcx);
                rustc_ty::Ty::new_array_with_const_len(tcx, ty, len)
            }
            TyKind::Param(pty) => rustc_ty::Ty::new_param(tcx, pty.index, pty.name),
            TyKind::Ref(re, ty, mutbl) => {
                rustc_ty::Ty::new_ref(tcx, re.to_rustc(tcx), ty.to_rustc(tcx), *mutbl)
            }
            TyKind::Tuple(tys) => {
                let ts = tys.iter().map(|ty| ty.to_rustc(tcx)).collect_vec();
                rustc_ty::Ty::new_tup(tcx, tcx.mk_type_list(&ts))
            }
            TyKind::Slice(ty) => rustc_ty::Ty::new_slice(tcx, ty.to_rustc(tcx)),
            TyKind::RawPtr(ty, mutbl) => rustc_ty::Ty::new_ptr(tcx, ty.to_rustc(tcx), *mutbl),
            TyKind::Closure(did, args) => rustc_ty::Ty::new_closure(tcx, *did, args.to_rustc(tcx)),
            TyKind::FnPtr(poly_sig) => rustc_ty::Ty::new_fn_ptr(tcx, poly_sig.to_rustc(tcx)),
            TyKind::Alias(kind, alias_ty) => {
                rustc_ty::Ty::new_alias(tcx, kind.to_rustc(tcx), alias_ty.to_rustc(tcx))
            }
            TyKind::Dynamic(exi_preds, re) => {
                let preds = exi_preds
                    .iter()
                    .map(|pred| pred.to_rustc(tcx))
                    .collect_vec();

                let preds = tcx.mk_poly_existential_predicates(&preds);
                rustc_ty::Ty::new_dynamic(tcx, preds, re.to_rustc(tcx))
            }
            TyKind::Coroutine(_, _) | TyKind::CoroutineWitness(_, _) => {
                bug!("TODO: to_rustc for `{self:?}`")
            }
        }
    }
}

impl_internable!(TyS, AdtDefData);
impl_slice_internable!(
    Ty,
    GenericArg,
    GenericParamDef,
    BoundVariableKind,
    Clause,
    ValTree,
    Binder<ExistentialPredicate>,
);

impl fmt::Debug for ExistentialPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExistentialPredicate::Trait(trait_ref) => write!(f, "{trait_ref:?}"),
            ExistentialPredicate::Projection(proj) => write!(f, "({proj:?})"),
            ExistentialPredicate::AutoTrait(def_id) => {
                write!(f, "{}", def_id_to_string(*def_id))
            }
        }
    }
}

impl fmt::Debug for ExistentialTraitRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", def_id_to_string(self.def_id))?;
        if !self.args.is_empty() {
            write!(f, "<{:?}>", self.args.iter().format(","))?;
        }
        Ok(())
    }
}

impl fmt::Debug for ExistentialProjection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", def_id_to_string(self.def_id))?;
        if !self.args.is_empty() {
            write!(f, "<{:?}>", self.args.iter().format(","))?;
        }
        write!(f, " = {:?}", &self.term)
    }
}

impl fmt::Debug for GenericArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GenericArg::Ty(ty) => write!(f, "{ty:?}"),
            GenericArg::Lifetime(region) => write!(f, "{region:?}"),
            GenericArg::Const(c) => write!(f, "Const({c:?})"),
        }
    }
}

impl fmt::Debug for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", region_to_string(*self))
    }
}

impl<T: fmt::Debug> fmt::Debug for Binder<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.1.is_empty() {
            write!(f, "for<{:?}> ", self.1.iter().format(", "))?;
        }
        write!(f, "{:?}", self.0)
    }
}

impl fmt::Debug for FnSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn({:?}) -> {:?}", self.inputs().iter().format(", "), self.output())
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TyKind::Adt(adt_def, args) => {
                let adt_name = rustc_middle::ty::tls::with(|tcx| tcx.def_path_str(adt_def.did()));
                write!(f, "{adt_name}")?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
                }
                Ok(())
            }
            TyKind::FnDef(def_id, args) => {
                write!(f, "FnDef({:?}[{:?}])", def_id, args.iter().format(", "))
            }
            TyKind::Bool => write!(f, "bool"),
            TyKind::Str => write!(f, "str"),
            TyKind::Char => write!(f, "char"),
            TyKind::Float(float_ty) => write!(f, "{}", float_ty.name_str()),
            TyKind::Int(int_ty) => write!(f, "{}", int_ty.name_str()),
            TyKind::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str()),
            TyKind::Never => write!(f, "!"),
            TyKind::Param(param_ty) => write!(f, "{param_ty}"),
            TyKind::Ref(region, ty, Mutability::Mut) => write!(f, "&{region:?} mut {ty:?}"),
            TyKind::Ref(region, ty, Mutability::Not) => write!(f, "&{region:?} {ty:?}"),
            TyKind::Array(ty, c) => write!(f, "[{ty:?}; {c:?}]"),
            TyKind::Tuple(tys) => {
                if let [ty] = &tys[..] {
                    write!(f, "({ty:?},)")
                } else {
                    write!(f, "({:?})", tys.iter().format(", "))
                }
            }
            TyKind::Slice(ty) => write!(f, "[{ty:?}]"),
            TyKind::RawPtr(ty, Mutability::Mut) => write!(f, "*mut {ty:?}"),
            TyKind::RawPtr(ty, Mutability::Not) => write!(f, "*const {ty:?}"),
            TyKind::FnPtr(fn_sig) => write!(f, "{fn_sig:?}"),
            TyKind::Closure(did, args) => {
                write!(f, "{}", def_id_to_string(*did))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
                }
                Ok(())
            }
            TyKind::Coroutine(did, args) => {
                write!(f, "{}", def_id_to_string(*did))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
                }
                Ok(())
            }
            TyKind::CoroutineWitness(did, args) => {
                write!(f, "{}", def_id_to_string(*did))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
                }
                Ok(())
            }
            TyKind::Alias(AliasKind::Opaque, alias_ty) => {
                write!(f, "{}", def_id_to_string(alias_ty.def_id))?;
                if !alias_ty.args.is_empty() {
                    write!(f, "<{:?}>", alias_ty.args.iter().format(", "))?;
                }
                Ok(())
            }
            TyKind::Alias(kind, alias_ty) => {
                let def_id = alias_ty.def_id;
                let args = &alias_ty.args;
                write!(f, "Alias ({kind:?}, {}, ", def_id_to_string(def_id))?;
                if !args.is_empty() {
                    write!(f, "<{:?}>", args.iter().format(", "))?;
                }
                write!(f, ")")?;
                Ok(())
            }
            TyKind::Dynamic(preds, r) => {
                write!(f, "dyn {:?} + {r:?}", preds.iter().format(", "))
            }
            TyKind::Foreign(def_id) => {
                write!(f, "Foreign {def_id:?}")
            }
        }
    }
}

impl fmt::Debug for ValTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            ValTree::Leaf(scalar_int) => write!(f, "Leaf({scalar_int})"),
            ValTree::Branch(vec) => write!(f, "Branch([{:?}])", vec.iter().format(", ")),
        }
    }
}

impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ConstKind::Param(p) => write!(f, "{}", p.name.as_str()),
            ConstKind::Value(_, v) => write!(f, "{v:?}"),
            ConstKind::Infer(infer_const) => write!(f, "{infer_const:?}"),
            ConstKind::Unevaluated(uneval_const) => write!(f, "{uneval_const:?}"),
        }
    }
}

pub fn region_to_string(region: Region) -> String {
    match region {
        Region::ReBound(debruijn, region) => {
            match region.kind {
                BoundRegionKind::Anon => "'<annon>".to_string(),
                BoundRegionKind::Named(_) => {
                    format!("{debruijn:?}{region:?}")
                }
                BoundRegionKind::ClosureEnv => "'<env>".to_string(),
                BoundRegionKind::NamedAnon(sym) => format!("{sym}"),
            }
        }
        Region::ReEarlyParam(region) => region.name.to_string(),
        Region::ReStatic => "'static".to_string(),
        Region::ReVar(rvid) => format!("{rvid:?}"),
        Region::ReLateParam(..) => "'<free>".to_string(),
        Region::ReErased => "'_".to_string(),
    }
}
