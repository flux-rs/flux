//! Defines how flux represents refinement types internally. Definitions in this module are used
//! during refinement type checking. A couple of important differences between definitions in this
//! module and in [`crate::fhir`] are:
//!
//! * Types in this module use debruijn indices to represent local binders.
//! * Data structures are interned so they can be cheaply cloned.
mod binder;
pub mod canonicalize;
pub mod evars;
mod expr;
pub mod fold;
pub(crate) mod normalize;
mod pretty;
pub mod projections;
pub mod refining;
pub mod subst;
use std::{borrow::Cow, cmp::Ordering, hash::Hash, iter, sync::LazyLock};

pub use binder::{Binder, BoundReftKind, BoundVariableKind, BoundVariableKinds, EarlyBinder};
pub use evars::{EVar, EVarGen};
pub use expr::{
    AggregateKind, AliasReft, BinOp, BoundReft, Constant, ESpan, EarlyReftParam, Expr, ExprKind,
    FieldProj, HoleKind, KVar, KVid, Lambda, Loc, Name, Path, Real, UnOp, Var,
};
pub use flux_arc_interner::List;
use flux_arc_interner::{impl_internable, impl_slice_internable, Interned};
use flux_common::{bug, tracked_span_bug};
use flux_macros::{TypeFoldable, TypeVisitable};
pub use flux_rustc_bridge::ty::{
    AliasKind, BoundRegion, BoundRegionKind, BoundVar, Const, ConstKind, ConstVid, DebruijnIndex,
    EarlyParamRegion, LateParamRegion, OutlivesPredicate,
    Region::{self, *},
    RegionVid,
};
use flux_rustc_bridge::{
    mir::Place,
    ty::{self, VariantDef},
    ToRustc,
};
use itertools::Itertools;
pub use normalize::SpecFuncDefns;
use rustc_data_structures::unord::UnordMap;
use rustc_hir::{def_id::DefId, LangItem, Safety};
use rustc_index::{newtype_index, IndexSlice};
use rustc_macros::{extension, Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::ty::{ParamConst, TyCtxt};
pub use rustc_middle::{
    mir::Mutability,
    ty::{AdtFlags, ClosureKind, FloatTy, IntTy, ParamTy, ScalarInt, UintTy},
};
use rustc_span::{sym, symbol::kw, Symbol};
pub use rustc_target::abi::{VariantIdx, FIRST_VARIANT};
use rustc_target::spec::abi;
pub use rustc_type_ir::{TyVid, INNERMOST};
pub use SortInfer::*;

use self::fold::TypeFoldable;
pub use crate::fhir::InferMode;
use crate::{
    fhir::{self, FhirId, FluxOwnerId, SpecFuncKind},
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::subst::SortSubst,
};

#[derive(Debug, Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtSortDef(Interned<AdtSortDefData>);

#[derive(Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
struct AdtSortDefData {
    def_id: DefId,
    params: Vec<ParamTy>,
    field_names: Vec<Symbol>,
    sorts: List<Sort>,
}

impl AdtSortDef {
    pub fn new(def_id: DefId, params: Vec<ParamTy>, fields: Vec<(Symbol, Sort)>) -> Self {
        let (field_names, sorts) = fields.into_iter().unzip();
        Self(Interned::new(AdtSortDefData {
            def_id,
            params,
            field_names,
            sorts: List::from_vec(sorts),
        }))
    }

    pub fn did(&self) -> DefId {
        self.0.def_id
    }

    pub fn fields(&self) -> usize {
        self.0.sorts.len()
    }

    pub fn projections(&self) -> impl Iterator<Item = FieldProj> + '_ {
        (0..self.fields()).map(|i| FieldProj::Adt { def_id: self.did(), field: i as u32 })
    }

    pub fn field_sort(&self, args: &[Sort], name: Symbol) -> Option<Sort> {
        let idx = self.field_index(name)?;
        Some(self.0.sorts[idx].fold_with(&mut SortSubst::new(args)))
    }

    pub fn field_sorts(&self, args: &[Sort]) -> List<Sort> {
        self.0.sorts.fold_with(&mut SortSubst::new(args))
    }

    pub fn sort(&self, args: &[GenericArg]) -> Sort {
        let sorts = self
            .filter_generic_args(args)
            .map(|arg| arg.expect_base().sort())
            .collect();

        Sort::App(SortCtor::Adt(self.clone()), sorts)
    }

    /// Given a list of generic args, returns an iterator of the generic arguments that should be
    /// mapped to sorts for instantiation.
    pub fn filter_generic_args<'a, A>(&'a self, args: &'a [A]) -> impl Iterator<Item = &A> + 'a {
        self.0.params.iter().map(|p| &args[p.index as usize])
    }

    pub fn identity_args(&self) -> List<Sort> {
        (0..self.0.params.len())
            .map(|i| Sort::Var(ParamSort::from(i)))
            .collect()
    }

    pub fn field_index(&self, name: Symbol) -> Option<usize> {
        self.0.field_names.iter().position(|it| name == *it)
    }
}

#[derive(Debug, Clone, Default, Encodable, Decodable)]
pub struct Generics {
    pub parent: Option<DefId>,
    pub parent_count: usize,
    pub own_params: List<GenericParamDef>,
    pub has_self: bool,
}

impl Generics {
    pub fn count(&self) -> usize {
        self.parent_count + self.own_params.len()
    }

    pub fn own_default_count(&self) -> usize {
        self.own_params
            .iter()
            .filter(|param| {
                match param.kind {
                    GenericParamDefKind::Type { has_default } => has_default,
                    GenericParamDefKind::Const { has_default } => has_default,
                    GenericParamDefKind::Base | GenericParamDefKind::Lifetime => false,
                }
            })
            .count()
    }

    pub fn param_at(&self, param_index: usize, genv: GlobalEnv) -> QueryResult<GenericParamDef> {
        if let Some(index) = param_index.checked_sub(self.parent_count) {
            Ok(self.own_params[index].clone())
        } else {
            let parent = self.parent.expect("parent_count > 0 but no parent?");
            genv.generics_of(parent)?.param_at(param_index, genv)
        }
    }

    pub fn const_params(&self, genv: GlobalEnv) -> QueryResult<Vec<(ParamConst, Sort)>> {
        // FIXME(nilehmann) this shouldn't use the methods in `flux_middle::sort_of` to get the sort
        let mut res = vec![];
        for i in 0..self.count() {
            let param = self.param_at(i, genv)?;
            if let GenericParamDefKind::Const { .. } = param.kind
                && let Some(sort) = genv.sort_of_generic_param(param.def_id)?
            {
                let param_const = ParamConst { name: param.name, index: param.index };
                res.push((param_const, sort));
            }
        }
        Ok(res)
    }
}

#[derive(Debug, Clone, TyEncodable, TyDecodable)]
pub struct RefinementGenerics {
    pub parent: Option<DefId>,
    pub parent_count: usize,
    pub params: List<RefineParam>,
}

#[derive(PartialEq, Eq, Debug, Clone, Hash, TyEncodable, TyDecodable)]
pub struct RefineParam {
    pub sort: Sort,
    pub name: Symbol,
    pub mode: InferMode,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Encodable, Decodable)]
pub struct GenericParamDef {
    pub kind: GenericParamDefKind,
    pub def_id: DefId,
    pub index: u32,
    pub name: Symbol,
}

#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum GenericParamDefKind {
    Type { has_default: bool },
    Base,
    Lifetime,
    Const { has_default: bool },
}

pub const SELF_PARAM_TY: ParamTy = ParamTy { index: 0, name: kw::SelfUpper };

#[derive(Debug, Clone, TyEncodable, TyDecodable)]
pub struct GenericPredicates {
    pub parent: Option<DefId>,
    pub predicates: List<Clause>,
}

#[derive(
    Debug, PartialEq, Eq, Hash, Clone, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct Clause {
    kind: Binder<ClauseKind>,
}

pub type Clauses = List<Clause>;

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub enum ClauseKind {
    FnTrait(FnTraitPredicate),
    Trait(TraitPredicate),
    Projection(ProjectionPredicate),
    TypeOutlives(TypeOutlivesPredicate),
    ConstArgHasType(Const, Ty),
    CoroutineOblig(CoroutineObligPredicate),
}

pub type TypeOutlivesPredicate = OutlivesPredicate<Ty>;

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
}

pub type PolyTraitPredicate = Binder<TraitPredicate>;

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct TraitRef {
    pub def_id: DefId,
    pub args: GenericArgs,
}

impl<'tcx> ToRustc<'tcx> for TraitRef {
    type T = rustc_middle::ty::TraitRef<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        rustc_middle::ty::TraitRef::new(tcx, self.def_id, self.args.to_rustc(tcx))
    }
}

pub type PolyTraitRef = Binder<TraitRef>;

impl PolyTraitRef {
    pub fn def_id(&self) -> DefId {
        self.as_ref().skip_binder().def_id
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable)]
pub enum ExistentialPredicate {
    Trait(ExistentialTraitRef),
    Projection(ExistentialProjection),
    AutoTrait(DefId),
}

pub type PolyExistentialPredicate = Binder<ExistentialPredicate>;

impl ExistentialPredicate {
    /// See [`rustc_middle::ty::ExistentialPredicateStableCmpExt`]
    pub fn stable_cmp(&self, tcx: TyCtxt, other: &Self) -> Ordering {
        match (self, other) {
            (ExistentialPredicate::Trait(_), ExistentialPredicate::Trait(_)) => Ordering::Equal,
            (ExistentialPredicate::Projection(a), ExistentialPredicate::Projection(b)) => {
                tcx.def_path_hash(a.def_id)
                    .cmp(&tcx.def_path_hash(b.def_id))
            }
            (ExistentialPredicate::AutoTrait(a), ExistentialPredicate::AutoTrait(b)) => {
                tcx.def_path_hash(*a).cmp(&tcx.def_path_hash(*b))
            }
            (ExistentialPredicate::Trait(_), _) => Ordering::Less,
            (ExistentialPredicate::Projection(_), ExistentialPredicate::Trait(_)) => {
                Ordering::Greater
            }
            (ExistentialPredicate::Projection(_), _) => Ordering::Less,
            (ExistentialPredicate::AutoTrait(_), _) => Ordering::Greater,
        }
    }
}

impl<'tcx> ToRustc<'tcx> for ExistentialPredicate {
    type T = rustc_middle::ty::ExistentialPredicate<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        match self {
            ExistentialPredicate::Trait(trait_ref) => {
                let trait_ref = rustc_middle::ty::ExistentialTraitRef {
                    def_id: trait_ref.def_id,
                    args: trait_ref.args.to_rustc(tcx),
                };
                rustc_middle::ty::ExistentialPredicate::Trait(trait_ref)
            }
            ExistentialPredicate::Projection(projection) => {
                rustc_middle::ty::ExistentialPredicate::Projection(
                    rustc_middle::ty::ExistentialProjection {
                        def_id: projection.def_id,
                        args: projection.args.to_rustc(tcx),
                        term: projection.term.to_rustc(tcx).into(),
                    },
                )
            }
            ExistentialPredicate::AutoTrait(def_id) => {
                rustc_middle::ty::ExistentialPredicate::AutoTrait(*def_id)
            }
        }
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct ExistentialTraitRef {
    pub def_id: DefId,
    pub args: GenericArgs,
}

pub type PolyExistentialTraitRef = Binder<ExistentialTraitRef>;

impl PolyExistentialTraitRef {
    pub fn def_id(&self) -> DefId {
        self.as_ref().skip_binder().def_id
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct ExistentialProjection {
    pub def_id: DefId,
    pub args: GenericArgs,
    pub term: Ty,
}

#[derive(
    PartialEq, Eq, Hash, Debug, Clone, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct ProjectionPredicate {
    pub projection_ty: AliasTy,
    pub term: Ty,
}

#[derive(
    Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct FnTraitPredicate {
    pub self_ty: Ty,
    pub tupled_args: Ty,
    pub output: Ty,
    pub kind: ClosureKind,
}

impl FnTraitPredicate {
    pub fn fndef_poly_sig(&self) -> PolyFnSig {
        let inputs = self.tupled_args.expect_tuple().iter().cloned().collect();

        let fn_sig = FnSig::new(
            Safety::Safe,
            abi::Abi::Rust,
            List::empty(),
            inputs,
            Binder::bind_with_vars(FnOutput::new(self.output.clone(), vec![]), List::empty()),
        );

        PolyFnSig::bind_with_vars(fn_sig, List::empty())
    }

    pub fn to_poly_fn_sig(&self, closure_id: DefId, tys: List<Ty>) -> PolyFnSig {
        let mut vars = vec![];

        let closure_ty = Ty::closure(closure_id, tys);
        let env_ty = match self.kind {
            ClosureKind::Fn => {
                vars.push(BoundVariableKind::Region(BoundRegionKind::BrEnv));
                let br = BoundRegion {
                    var: BoundVar::from_usize(vars.len() - 1),
                    kind: BoundRegionKind::BrEnv,
                };
                Ty::mk_ref(ReBound(INNERMOST, br), closure_ty, Mutability::Not)
            }
            ClosureKind::FnMut => {
                vars.push(BoundVariableKind::Region(BoundRegionKind::BrEnv));
                let br = BoundRegion {
                    var: BoundVar::from_usize(vars.len() - 1),
                    kind: BoundRegionKind::BrEnv,
                };
                Ty::mk_ref(ReBound(INNERMOST, br), closure_ty, Mutability::Mut)
            }
            ClosureKind::FnOnce => closure_ty,
        };
        let inputs = std::iter::once(env_ty)
            .chain(self.tupled_args.expect_tuple().iter().cloned())
            .collect();

        let fn_sig = FnSig::new(
            Safety::Safe,
            abi::Abi::RustCall,
            List::empty(),
            inputs,
            Binder::bind_with_vars(FnOutput::new(self.output.clone(), vec![]), List::empty()),
        );

        PolyFnSig::bind_with_vars(fn_sig, List::from(vars))
    }
}

#[derive(
    Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct CoroutineObligPredicate {
    pub def_id: DefId,
    pub resume_ty: Ty,
    pub upvar_tys: List<Ty>,
    pub output: Ty,
}

#[derive(Debug, Clone, Encodable, Decodable)]
pub struct AssocRefinements {
    pub items: List<AssocRefinement>,
}

impl Default for AssocRefinements {
    fn default() -> Self {
        Self { items: List::empty() }
    }
}

impl AssocRefinements {
    pub fn find(&self, name: Symbol) -> Option<&AssocRefinement> {
        self.items.iter().find(|it| it.name == name)
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Encodable, Decodable)]
pub struct AssocRefinement {
    /// [`DefId`] of the container, i.e., the impl block or trait.
    pub container_def_id: DefId,
    pub name: Symbol,
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum SortCtor {
    Set,
    Map,
    Adt(AdtSortDef),
    User { name: Symbol },
}

newtype_index! {
    /// [ParamSort] is used for polymorphic sorts (Set, Map etc.) and [bit-vector size parameters].
    /// They should occur "bound" under a [`PolyFuncSort`]; i.e. should be < than the number of params
    /// in the [`PolyFuncSort`].
    ///
    /// [bit-vector size parameters]: BvSize::Param
    #[debug_format = "?{}s"]
    #[encodable]
    pub struct ParamSort {}
}

newtype_index! {
    /// A *sort* *v*variable *id*
    #[debug_format = "?{}s"]
    #[encodable]
    pub struct SortVid {}
}

impl ena::unify::UnifyKey for SortVid {
    type Value = Option<Sort>;

    #[inline]
    fn index(&self) -> u32 {
        self.as_u32()
    }

    #[inline]
    fn from_index(u: u32) -> Self {
        SortVid::from_u32(u)
    }

    fn tag() -> &'static str {
        "SortVid"
    }
}

impl ena::unify::EqUnifyValue for Sort {}

newtype_index! {
    /// A *num*eric *v*variable *id*
    #[debug_format = "?{}n"]
    #[encodable]
    pub struct NumVid {}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumVarValue {
    Real,
    Int,
}

impl NumVarValue {
    pub fn to_sort(self) -> Sort {
        match self {
            NumVarValue::Real => Sort::Real,
            NumVarValue::Int => Sort::Int,
        }
    }
}

impl ena::unify::UnifyKey for NumVid {
    type Value = Option<NumVarValue>;

    #[inline]
    fn index(&self) -> u32 {
        self.as_u32()
    }

    #[inline]
    fn from_index(u: u32) -> Self {
        NumVid::from_u32(u)
    }

    fn tag() -> &'static str {
        "NumVid"
    }
}

impl ena::unify::EqUnifyValue for NumVarValue {}

/// A placeholder for a sort that needs to be inferred
#[derive(PartialEq, Eq, Clone, Copy, Hash, Encodable, Decodable)]
pub enum SortInfer {
    /// A sort variable.
    SortVar(SortVid),
    /// A numeric sort variable.
    NumVar(NumVid),
}

newtype_index! {
    /// A *b*it *v*ector *size* *v*variable *id*
    #[debug_format = "?{}size"]
    #[encodable]
    pub struct BvSizeVid {}
}

impl ena::unify::UnifyKey for BvSizeVid {
    type Value = Option<BvSize>;

    #[inline]
    fn index(&self) -> u32 {
        self.as_u32()
    }

    #[inline]
    fn from_index(u: u32) -> Self {
        BvSizeVid::from_u32(u)
    }

    fn tag() -> &'static str {
        "BvSizeVid"
    }
}

impl ena::unify::EqUnifyValue for BvSize {}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum Sort {
    Int,
    Bool,
    Real,
    BitVec(BvSize),
    Str,
    Loc,
    Param(ParamTy),
    Tuple(List<Sort>),
    Func(PolyFuncSort),
    App(SortCtor, List<Sort>),
    Var(ParamSort),
    Infer(SortInfer),
    Err,
}

impl Sort {
    pub fn tuple(sorts: impl Into<List<Sort>>) -> Self {
        Sort::Tuple(sorts.into())
    }

    pub fn app(ctor: SortCtor, sorts: List<Sort>) -> Self {
        Sort::App(ctor, sorts)
    }

    pub fn unit() -> Self {
        Self::tuple(vec![])
    }

    #[track_caller]
    pub fn expect_func(&self) -> &PolyFuncSort {
        if let Sort::Func(sort) = self {
            sort
        } else {
            bug!("expected `Sort::Func`")
        }
    }

    pub fn is_loc(&self) -> bool {
        matches!(self, Sort::Loc)
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Sort::Tuple(sorts) if sorts.is_empty())
    }

    pub fn is_unit_adt(&self) -> Option<DefId> {
        if let Sort::App(SortCtor::Adt(sort_def), _) = self
            && sort_def.fields() == 0
        {
            Some(sort_def.did())
        } else {
            None
        }
    }

    /// Whether the sort is a function with return sort bool
    pub fn is_pred(&self) -> bool {
        matches!(self, Sort::Func(fsort) if fsort.skip_binders().output().is_bool())
    }

    /// Returns `true` if the sort is [`Bool`].
    ///
    /// [`Bool`]: Sort::Bool
    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self, Self::Int | Self::Real)
    }

    pub fn walk(&self, mut f: impl FnMut(&Sort, &[FieldProj])) {
        fn go(sort: &Sort, f: &mut impl FnMut(&Sort, &[FieldProj]), proj: &mut Vec<FieldProj>) {
            match sort {
                Sort::Tuple(flds) => {
                    for (i, sort) in flds.iter().enumerate() {
                        proj.push(FieldProj::Tuple { arity: flds.len(), field: i as u32 });
                        go(sort, f, proj);
                        proj.pop();
                    }
                }
                Sort::App(SortCtor::Adt(sort_def), args) => {
                    for (i, sort) in sort_def.field_sorts(args).iter().enumerate() {
                        proj.push(FieldProj::Adt { def_id: sort_def.did(), field: i as u32 });
                        go(sort, f, proj);
                        proj.pop();
                    }
                }
                _ => {
                    f(sort, proj);
                }
            }
        }
        go(self, &mut f, &mut vec![]);
    }
}

/// The size of a [bit-vector]
///
/// [bit-vector]: Sort::BitVec
#[derive(Clone, Copy, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum BvSize {
    /// A fixed size
    Fixed(usize),
    /// A size that has been parameterized, e.g., bound under a [`PolyFuncSort`]
    Param(ParamSort),
    /// A size that needs to be inferred. Used during sort checking to instantiate bit-vector
    /// sizes at call-sites.
    Infer(BvSizeVid),
}

impl rustc_errors::IntoDiagArg for Sort {
    fn into_diag_arg(self) -> rustc_errors::DiagArgValue {
        rustc_errors::DiagArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

impl rustc_errors::IntoDiagArg for FuncSort {
    fn into_diag_arg(self) -> rustc_errors::DiagArgValue {
        rustc_errors::DiagArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable)]
pub struct FuncSort {
    pub inputs_and_output: List<Sort>,
}

impl FuncSort {
    pub fn new(mut inputs: Vec<Sort>, output: Sort) -> Self {
        inputs.push(output);
        FuncSort { inputs_and_output: List::from_vec(inputs) }
    }

    pub fn inputs(&self) -> &[Sort] {
        &self.inputs_and_output[0..self.inputs_and_output.len() - 1]
    }

    pub fn output(&self) -> &Sort {
        &self.inputs_and_output[self.inputs_and_output.len() - 1]
    }

    pub fn to_poly(&self) -> PolyFuncSort {
        PolyFuncSort::new(List::empty(), self.clone())
    }
}

/// See [`PolyFuncSort`]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub enum SortParamKind {
    Sort,
    BvSize,
}

/// A polymorphic function sort parametric over [sorts] or [bit-vector sizes].
///
/// Parameterizing over bit-vector sizes is a bit of a stretch, because smtlib doesn't support full
/// parametric reasoning over them. As long as we used functions parameterized over a size monomorphically
/// we should be fine. Right now, we can guarantee this, because size parameters are not exposed in
/// the surface syntax and they are only used for predefined (interpreted) theory functions.
///
/// [sorts]: Sort
/// [bit-vector sizes]: BvSize::Param
#[derive(Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable)]
pub struct PolyFuncSort {
    /// The list of parameters including sorts and bit vector sizes
    params: List<SortParamKind>,
    fsort: FuncSort,
}

impl PolyFuncSort {
    pub fn new(params: List<SortParamKind>, fsort: FuncSort) -> Self {
        PolyFuncSort { params, fsort }
    }

    pub fn skip_binders(&self) -> FuncSort {
        self.fsort.clone()
    }

    pub fn instantiate_identity(&self) -> FuncSort {
        self.fsort.clone()
    }

    pub fn expect_mono(&self) -> FuncSort {
        assert!(self.params.is_empty());
        self.fsort.clone()
    }

    pub fn params(&self) -> impl ExactSizeIterator<Item = SortParamKind> + '_ {
        self.params.iter().copied()
    }

    pub fn instantiate(&self, args: &[SortArg]) -> FuncSort {
        self.fsort.fold_with(&mut SortSubst::new(args))
    }
}

/// An argument for a generic parameter in a [`Sort`] which can be either a generic sort or a
/// generic bit-vector size.
#[derive(
    Debug, Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub enum SortArg {
    Sort(Sort),
    BvSize(BvSize),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtDef(Interned<AdtDefData>);

#[derive(Debug, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtDefData {
    invariants: Vec<Invariant>,
    sort_def: AdtSortDef,
    opaque: bool,
    rustc: ty::AdtDef,
}

/// Option-like enum to explicitly mark that we don't have information about an ADT because it was
/// annotated with `#[flux::opaque]`. Note that only structs can be marked as opaque.
#[derive(Clone, Debug, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable)]
pub enum Opaqueness<T> {
    Opaque,
    Transparent(T),
}

pub static INT_TYS: [IntTy; 6] =
    [IntTy::Isize, IntTy::I8, IntTy::I16, IntTy::I32, IntTy::I64, IntTy::I128];
pub static UINT_TYS: [UintTy; 6] =
    [UintTy::Usize, UintTy::U8, UintTy::U16, UintTy::U32, UintTy::U64, UintTy::U128];

#[derive(
    Debug, Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable,
)]
pub struct Invariant {
    // This predicate may have sort variables, but we don't explicitly mark it like in `PolyFuncSort`.
    // See comment on `apply` for details.
    pred: Binder<Expr>,
}

impl Invariant {
    pub fn new(pred: Binder<Expr>) -> Self {
        Self { pred }
    }

    pub fn apply(&self, idx: &Expr) -> Expr {
        // The predicate may have sort variables but we don't explicitly instantiate them. This
        // works because within an expression, sort variables can only appear inside the sort
        // annotation for a lambda and invariants cannot have lambdas. It remains to instantiate
        // variables in the sort of the binder itself, but since we are removing it, we can avoid
        // the explicit instantiation. Ultimately, this works because the expression we generate in
        // fixpoint doesn't need sort annotations (sorts are re-inferred).
        self.pred.replace_bound_reft(idx)
    }
}

pub type PolyVariants = List<Binder<VariantSig>>;
pub type PolyVariant = Binder<VariantSig>;

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct VariantSig {
    pub adt_def: AdtDef,
    pub args: GenericArgs,
    pub fields: List<Ty>,
    pub idx: Expr,
}

pub type PolyFnSig = Binder<FnSig>;

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable)]
pub struct FnSig {
    safety: Safety,
    abi: abi::Abi,
    requires: List<Expr>,
    inputs: List<Ty>,
    output: Binder<FnOutput>,
}

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct FnOutput {
    pub ret: Ty,
    pub ensures: List<Ensures>,
}

#[derive(Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub enum Ensures {
    Type(Path, Ty),
    Pred(Expr),
}

#[derive(Debug, TypeVisitable, TypeFoldable)]
pub struct Qualifier {
    pub name: Symbol,
    pub body: Binder<Expr>,
    pub global: bool,
}

pub struct SpecFunc {
    pub name: Symbol,
    pub expr: Binder<Expr>,
}

#[derive(Debug, Clone)]
pub struct SpecFuncDecl {
    pub name: Symbol,
    pub sort: PolyFuncSort,
    pub kind: SpecFuncKind,
}

#[derive(Debug)]
pub struct ClosureOblig {
    pub oblig_def_id: DefId,
    pub oblig_sig: PolyFnSig,
}

pub type TyCtor = Binder<Ty>;

impl TyCtor {
    pub fn to_ty(&self) -> Ty {
        match &self.vars()[..] {
            [] => return self.skip_binder_ref().shift_out_escaping(1),
            [BoundVariableKind::Refine(sort, ..)] => {
                if sort.is_unit() {
                    return self.replace_bound_reft(&Expr::unit());
                }
                if let Some(def_id) = sort.is_unit_adt() {
                    return self.replace_bound_reft(&Expr::unit_adt(def_id));
                }
            }
            _ => {}
        }
        Ty::exists(self.clone())
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct Ty(Interned<TyKind>);

impl Ty {
    pub fn kind(&self) -> &TyKind {
        &self.0
    }

    /// Dummy type used for the `Self` of a `TraitRef` created when converting a trait object, and
    /// which gets removed in `ExistentialTraitRef`. This type must not appear anywhere in other
    /// converted types and must be a valid `rustc` type (i.e., we must be able to call `to_rustc`
    /// on it). `TyKind::Infer(TyVid(0))` does the job, with the caveat that we must skip 0 when
    /// generating `TyKind::Infer` for "type holes".
    pub fn trait_object_dummy_self() -> Ty {
        Ty::infer(TyVid::from_u32(0))
    }

    pub fn alias(kind: AliasKind, alias_ty: AliasTy) -> Ty {
        TyKind::Alias(kind, alias_ty).intern()
    }

    pub fn opaque(def_id: impl Into<DefId>, args: GenericArgs, refine_args: RefineArgs) -> Ty {
        TyKind::Alias(AliasKind::Opaque, AliasTy { def_id: def_id.into(), args, refine_args })
            .intern()
    }

    pub fn projection(alias_ty: AliasTy) -> Ty {
        Self::alias(AliasKind::Projection, alias_ty)
    }

    pub fn dynamic(preds: impl Into<List<Binder<ExistentialPredicate>>>, region: Region) -> Ty {
        BaseTy::Dynamic(preds.into(), region).to_ty()
    }

    pub fn strg_ref(re: Region, path: Path, ty: Ty) -> Ty {
        TyKind::StrgRef(re, path, ty).intern()
    }

    pub fn ptr(pk: impl Into<PtrKind>, path: impl Into<Path>) -> Ty {
        TyKind::Ptr(pk.into(), path.into()).intern()
    }

    pub fn constr(p: impl Into<Expr>, ty: Ty) -> Ty {
        TyKind::Constr(p.into(), ty).intern()
    }

    pub fn uninit() -> Ty {
        TyKind::Uninit.intern()
    }

    pub fn indexed(bty: BaseTy, idx: impl Into<Expr>) -> Ty {
        TyKind::Indexed(bty, idx.into()).intern()
    }

    pub fn exists(ty: Binder<Ty>) -> Ty {
        TyKind::Exists(ty).intern()
    }

    pub fn exists_with_constr(bty: BaseTy, pred: Expr) -> Ty {
        let sort = bty.sort();
        let ty = Ty::indexed(bty, Expr::nu());
        Ty::exists(Binder::bind_with_sort(Ty::constr(pred, ty), sort))
    }

    pub fn discr(adt_def: AdtDef, place: Place) -> Ty {
        TyKind::Discr(adt_def, place).intern()
    }

    pub fn unit() -> Ty {
        Ty::tuple(vec![])
    }

    pub fn bool() -> Ty {
        BaseTy::Bool.to_ty()
    }

    pub fn int(int_ty: IntTy) -> Ty {
        BaseTy::Int(int_ty).to_ty()
    }

    pub fn uint(uint_ty: UintTy) -> Ty {
        BaseTy::Uint(uint_ty).to_ty()
    }

    pub fn param(param_ty: ParamTy) -> Ty {
        TyKind::Param(param_ty).intern()
    }

    pub fn downcast(
        adt: AdtDef,
        args: GenericArgs,
        ty: Ty,
        variant: VariantIdx,
        fields: List<Ty>,
    ) -> Ty {
        TyKind::Downcast(adt, args, ty, variant, fields).intern()
    }

    pub fn blocked(ty: Ty) -> Ty {
        TyKind::Blocked(ty).intern()
    }

    pub fn str() -> Ty {
        BaseTy::Str.to_ty()
    }

    pub fn char() -> Ty {
        BaseTy::Char.to_ty()
    }

    pub fn float(float_ty: FloatTy) -> Ty {
        BaseTy::Float(float_ty).to_ty()
    }

    pub fn mk_ref(region: Region, ty: Ty, mutbl: Mutability) -> Ty {
        BaseTy::Ref(region, ty, mutbl).to_ty()
    }

    pub fn mk_slice(ty: Ty) -> Ty {
        BaseTy::Slice(ty).to_ty()
    }

    pub fn mk_box(genv: GlobalEnv, deref_ty: Ty, alloc_ty: Ty) -> QueryResult<Ty> {
        let def_id = genv.tcx().require_lang_item(LangItem::OwnedBox, None);
        let adt_def = genv.adt_def(def_id)?;

        let args = vec![GenericArg::Ty(deref_ty), GenericArg::Ty(alloc_ty)];

        let bty = BaseTy::adt(adt_def, args);
        Ok(Ty::indexed(bty, Expr::unit_adt(def_id)))
    }

    pub fn mk_box_with_default_alloc(genv: GlobalEnv, deref_ty: Ty) -> QueryResult<Ty> {
        let def_id = genv.tcx().require_lang_item(LangItem::OwnedBox, None);

        let generics = genv.generics_of(def_id)?;
        let alloc_ty = genv.refine_default(
            &generics,
            &genv
                .lower_type_of(generics.own_params[1].def_id)?
                .skip_binder(),
        )?;

        Ty::mk_box(genv, deref_ty, alloc_ty)
    }

    pub fn tuple(tys: impl Into<List<Ty>>) -> Ty {
        BaseTy::Tuple(tys.into()).to_ty()
    }

    pub fn array(ty: Ty, c: Const) -> Ty {
        BaseTy::Array(ty, c).to_ty()
    }

    pub fn closure(did: DefId, tys: impl Into<List<Ty>>) -> Ty {
        BaseTy::Closure(did, tys.into()).to_ty()
    }

    pub fn coroutine(did: DefId, resume_ty: Ty, upvar_tys: List<Ty>) -> Ty {
        BaseTy::Coroutine(did, resume_ty, upvar_tys).to_ty()
    }

    pub fn never() -> Ty {
        BaseTy::Never.to_ty()
    }

    pub fn infer(vid: TyVid) -> Ty {
        TyKind::Infer(vid).intern()
    }

    pub fn unconstr(&self) -> (Ty, Expr) {
        fn go(this: &Ty, preds: &mut Vec<Expr>) -> Ty {
            if let TyKind::Constr(pred, ty) = this.kind() {
                preds.push(pred.clone());
                go(ty, preds)
            } else {
                this.clone()
            }
        }
        let mut preds = vec![];
        (go(self, &mut preds), Expr::and_from_iter(preds))
    }

    pub fn unblocked(&self) -> Ty {
        match self.kind() {
            TyKind::Blocked(ty) => ty.clone(),
            _ => self.clone(),
        }
    }

    /// Whether the type is an `int` or a `uint`
    pub fn is_integral(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_integral)
            .unwrap_or_default()
    }

    /// Whether the type is a `bool`
    pub fn is_bool(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_bool)
            .unwrap_or_default()
    }

    pub fn is_uninit(&self) -> bool {
        matches!(self.kind(), TyKind::Uninit)
    }

    pub fn is_box(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_box)
            .unwrap_or_default()
    }

    pub fn is_struct(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_struct)
            .unwrap_or_default()
    }

    pub fn is_array(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_array)
            .unwrap_or_default()
    }

    pub fn is_slice(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_slice)
            .unwrap_or_default()
    }

    pub fn as_bty_skipping_existentials(&self) -> Option<&BaseTy> {
        match self.kind() {
            TyKind::Indexed(bty, _) => Some(bty),
            TyKind::Exists(ty) => Some(ty.skip_binder_ref().as_bty_skipping_existentials()?),
            TyKind::Constr(_, ty) => ty.as_bty_skipping_existentials(),
            _ => None,
        }
    }

    #[track_caller]
    pub fn expect_discr(&self) -> (&AdtDef, &Place) {
        if let TyKind::Discr(adt_def, place) = self.kind() {
            (adt_def, place)
        } else {
            tracked_span_bug!("expected discr")
        }
    }

    #[track_caller]
    pub fn expect_adt(&self) -> (&AdtDef, &[GenericArg], &Expr) {
        if let TyKind::Indexed(BaseTy::Adt(adt_def, args), idx) = self.kind() {
            (adt_def, args, idx)
        } else {
            tracked_span_bug!("expected adt `{self:?}`")
        }
    }

    #[track_caller]
    pub(crate) fn expect_tuple(&self) -> &[Ty] {
        if let TyKind::Indexed(BaseTy::Tuple(tys), _) = self.kind() {
            tys
        } else {
            tracked_span_bug!("expected tuple found `{self:?}` (kind: `{:?}`)", self.kind())
        }
    }
}

impl<'tcx> ToRustc<'tcx> for Ty {
    type T = rustc_middle::ty::Ty<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        match self.kind() {
            TyKind::Indexed(bty, _) => bty.to_rustc(tcx),
            TyKind::Exists(ty) => ty.skip_binder_ref().to_rustc(tcx),
            TyKind::Constr(_, ty) => ty.to_rustc(tcx),
            TyKind::Param(pty) => pty.to_ty(tcx),
            TyKind::Alias(kind, alias_ty) => {
                rustc_middle::ty::Ty::new_alias(tcx, kind.to_rustc(tcx), alias_ty.to_rustc(tcx))
            }
            TyKind::StrgRef(re, _, ty) => {
                rustc_middle::ty::Ty::new_ref(
                    tcx,
                    re.to_rustc(tcx),
                    ty.to_rustc(tcx),
                    Mutability::Mut,
                )
            }
            TyKind::Infer(vid) => rustc_middle::ty::Ty::new_var(tcx, *vid),
            TyKind::Uninit
            | TyKind::Ptr(_, _)
            | TyKind::Discr(_, _)
            | TyKind::Downcast(_, _, _, _, _)
            | TyKind::Blocked(_) => bug!(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, Debug)]
pub enum TyKind {
    Indexed(BaseTy, Expr),
    Exists(Binder<Ty>),
    Constr(Expr, Ty),
    Uninit,
    StrgRef(Region, Path, Ty),
    Ptr(PtrKind, Path),
    /// This is a bit of a hack. We use this type internally to represent the result of
    /// [`Rvalue::Discriminant`] in a way that we can recover the necessary control information
    /// when checking a [`match`]. The hack is that we assume the dicriminant remains the same from
    /// the creation of this type until we use it in a [`match`].
    ///
    ///
    /// [`Rvalue::Discriminant`]: flux_rustc_bridge::mir::Rvalue::Discriminant
    /// [`match`]: flux_rustc_bridge::mir::TerminatorKind::SwitchInt
    Discr(AdtDef, Place),
    Param(ParamTy),
    Downcast(AdtDef, GenericArgs, Ty, VariantIdx, List<Ty>),
    Blocked(Ty),
    Alias(AliasKind, AliasTy),
    /// A type that needs to be inferred by matching the signature against a rust signature.
    /// [`TyKind::Infer`] appear as an intermediate step during `conv` and should not be present in
    /// the final signature.
    Infer(TyVid),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum PtrKind {
    Mut(Region),
    Box,
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Str,
    Char,
    Slice(Ty),
    Adt(AdtDef, GenericArgs),
    Float(FloatTy),
    RawPtr(Ty, Mutability),
    Ref(Region, Ty, Mutability),
    FnPtr(PolyFnSig),
    FnDef(DefId, GenericArgs),
    Tuple(List<Ty>),
    Array(Ty, Const),
    Never,
    Closure(DefId, /* upvar_tys */ List<Ty>),
    Coroutine(DefId, /*resume_ty: */ Ty, /* upvar_tys: */ List<Ty>),
    Dynamic(List<Binder<ExistentialPredicate>>, Region),
    Param(ParamTy),
}

impl BaseTy {
    pub fn adt(adt_def: AdtDef, args: impl Into<GenericArgs>) -> BaseTy {
        BaseTy::Adt(adt_def, args.into())
    }

    pub fn fn_def(def_id: DefId, args: impl Into<GenericArgs>) -> BaseTy {
        BaseTy::FnDef(def_id, args.into())
    }

    pub fn from_primitive_str(s: &str) -> Option<BaseTy> {
        match s {
            "i8" => Some(BaseTy::Int(IntTy::I8)),
            "i16" => Some(BaseTy::Int(IntTy::I16)),
            "i32" => Some(BaseTy::Int(IntTy::I32)),
            "i64" => Some(BaseTy::Int(IntTy::I64)),
            "i128" => Some(BaseTy::Int(IntTy::I128)),
            "u8" => Some(BaseTy::Uint(UintTy::U8)),
            "u16" => Some(BaseTy::Uint(UintTy::U16)),
            "u32" => Some(BaseTy::Uint(UintTy::U32)),
            "u64" => Some(BaseTy::Uint(UintTy::U64)),
            "u128" => Some(BaseTy::Uint(UintTy::U128)),
            "f16" => Some(BaseTy::Float(FloatTy::F16)),
            "f32" => Some(BaseTy::Float(FloatTy::F32)),
            "f64" => Some(BaseTy::Float(FloatTy::F64)),
            "f128" => Some(BaseTy::Float(FloatTy::F128)),
            "isize" => Some(BaseTy::Int(IntTy::Isize)),
            "usize" => Some(BaseTy::Uint(UintTy::Usize)),
            "bool" => Some(BaseTy::Bool),
            "char" => Some(BaseTy::Char),
            "str" => Some(BaseTy::Str),
            _ => None,
        }
    }

    /// If `self` is a primitive, return its [`Symbol`].
    pub fn primitive_symbol(&self) -> Option<Symbol> {
        match self {
            BaseTy::Bool => Some(sym::bool),
            BaseTy::Char => Some(sym::char),
            BaseTy::Float(f) => {
                match f {
                    FloatTy::F16 => Some(sym::f16),
                    FloatTy::F32 => Some(sym::f32),
                    FloatTy::F64 => Some(sym::f64),
                    FloatTy::F128 => Some(sym::f128),
                }
            }
            BaseTy::Int(f) => {
                match f {
                    IntTy::Isize => Some(sym::isize),
                    IntTy::I8 => Some(sym::i8),
                    IntTy::I16 => Some(sym::i16),
                    IntTy::I32 => Some(sym::i32),
                    IntTy::I64 => Some(sym::i64),
                    IntTy::I128 => Some(sym::i128),
                }
            }
            BaseTy::Uint(f) => {
                match f {
                    UintTy::Usize => Some(sym::usize),
                    UintTy::U8 => Some(sym::u8),
                    UintTy::U16 => Some(sym::u16),
                    UintTy::U32 => Some(sym::u32),
                    UintTy::U64 => Some(sym::u64),
                    UintTy::U128 => Some(sym::u128),
                }
            }
            BaseTy::Str => Some(sym::str),
            _ => None,
        }
    }

    pub fn is_integral(&self) -> bool {
        matches!(self, BaseTy::Int(_) | BaseTy::Uint(_))
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self, BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Float(_))
    }

    pub fn is_signed(&self) -> bool {
        matches!(self, BaseTy::Int(_))
    }

    pub fn is_unsigned(&self) -> bool {
        matches!(self, BaseTy::Uint(_))
    }

    pub fn is_float(&self) -> bool {
        matches!(self, BaseTy::Float(_))
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, BaseTy::Bool)
    }

    fn is_struct(&self) -> bool {
        matches!(self, BaseTy::Adt(adt_def, _) if adt_def.is_struct())
    }

    fn is_array(&self) -> bool {
        matches!(self, BaseTy::Array(..))
    }

    fn is_slice(&self) -> bool {
        matches!(self, BaseTy::Slice(..))
    }

    fn is_adt(&self) -> bool {
        matches!(self, BaseTy::Adt(..))
    }

    pub fn is_box(&self) -> bool {
        matches!(self, BaseTy::Adt(adt_def, _) if adt_def.is_box())
    }

    pub fn unpack_box(&self) -> Option<(&Ty, &Ty)> {
        if let BaseTy::Adt(adt_def, args) = self
            && adt_def.is_box()
        {
            Some(args.box_args())
        } else {
            None
        }
    }

    pub fn invariants(&self, overflow_checking: bool) -> &[Invariant] {
        match self {
            BaseTy::Adt(adt_def, _) => adt_def.invariants(),
            BaseTy::Uint(uint_ty) => uint_invariants(*uint_ty, overflow_checking),
            BaseTy::Int(int_ty) => int_invariants(*int_ty, overflow_checking),
            _ => &[],
        }
    }

    pub fn to_ty(&self) -> Ty {
        let sort = self.sort();
        if sort.is_unit() {
            Ty::indexed(self.clone(), Expr::unit())
        } else {
            Ty::exists(Binder::bind_with_sort(Ty::indexed(self.clone(), Expr::nu()), sort))
        }
    }

    pub fn sort(&self) -> Sort {
        match self {
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Slice(_) => Sort::Int,
            BaseTy::Bool => Sort::Bool,
            BaseTy::Adt(adt_def, args) => adt_def.sort(args),
            BaseTy::Param(param_ty) => Sort::Param(*param_ty),
            BaseTy::Str => Sort::Str,
            BaseTy::Float(_)
            | BaseTy::Char
            | BaseTy::RawPtr(..)
            | BaseTy::Ref(..)
            | BaseTy::FnPtr(..)
            | BaseTy::FnDef(..)
            | BaseTy::Tuple(_)
            | BaseTy::Array(_, _)
            | BaseTy::Closure(_, _)
            | BaseTy::Coroutine(..)
            | BaseTy::Dynamic(_, _)
            | BaseTy::Never => Sort::unit(),
        }
    }

    #[track_caller]
    pub fn expect_adt(&self) -> (&AdtDef, &[GenericArg]) {
        if let BaseTy::Adt(adt_def, args) = self {
            (adt_def, args)
        } else {
            tracked_span_bug!("expected adt `{self:?}`")
        }
    }
}

impl<'tcx> ToRustc<'tcx> for BaseTy {
    type T = rustc_middle::ty::Ty<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        use rustc_middle::ty;
        match self {
            BaseTy::Int(i) => ty::Ty::new_int(tcx, *i),
            BaseTy::Uint(i) => ty::Ty::new_uint(tcx, *i),
            BaseTy::Param(pty) => pty.to_ty(tcx),
            BaseTy::Slice(ty) => ty::Ty::new_slice(tcx, ty.to_rustc(tcx)),
            BaseTy::Bool => tcx.types.bool,
            BaseTy::Char => tcx.types.char,
            BaseTy::Str => tcx.types.str_,
            BaseTy::Adt(adt_def, args) => {
                let did = adt_def.did();
                let adt_def = tcx.adt_def(did);
                let args = args.to_rustc(tcx);
                ty::Ty::new_adt(tcx, adt_def, args)
            }
            BaseTy::FnDef(def_id, args) => {
                let args = args.to_rustc(tcx);
                ty::Ty::new_fn_def(tcx, *def_id, args)
            }
            BaseTy::Float(f) => ty::Ty::new_float(tcx, *f),
            BaseTy::RawPtr(ty, mutbl) => ty::Ty::new_ptr(tcx, ty.to_rustc(tcx), *mutbl),
            BaseTy::Ref(re, ty, mutbl) => {
                ty::Ty::new_ref(tcx, re.to_rustc(tcx), ty.to_rustc(tcx), *mutbl)
            }
            BaseTy::FnPtr(poly_sig) => ty::Ty::new_fn_ptr(tcx, poly_sig.to_rustc(tcx)),
            BaseTy::Tuple(tys) => {
                let ts = tys.iter().map(|ty| ty.to_rustc(tcx)).collect_vec();
                ty::Ty::new_tup(tcx, &ts)
            }
            BaseTy::Array(ty, n) => {
                let ty = ty.to_rustc(tcx);
                let n = n.to_rustc(tcx);
                ty::Ty::new_array_with_const_len(tcx, ty, n)
            }
            BaseTy::Never => tcx.types.never,
            BaseTy::Closure(_, _) => {
                bug!()
            }
            BaseTy::Dynamic(exi_preds, re) => {
                let preds: Vec<_> = exi_preds
                    .iter()
                    .map(|pred| pred.to_rustc(tcx))
                    .collect_vec();
                let preds = tcx.mk_poly_existential_predicates(&preds);
                ty::Ty::new_dynamic(tcx, preds, re.to_rustc(tcx), rustc_middle::ty::DynKind::Dyn)
            }
            BaseTy::Coroutine(def_id, resume_ty, upvars) => {
                bug!("TODO: Generator {def_id:?} {resume_ty:?} {upvars:?}")
                // let args = args.iter().map(|arg| into_rustc_generic_arg(tcx, arg));
                // let args = tcx.mk_args_from_iter(args);
                // ty::Ty::new_generator(*tcx, *def_id, args, mov)
            }
        }
    }
}

#[derive(
    Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct AliasTy {
    pub args: GenericArgs,
    /// Holds the refinement-arguments for opaque-types; empty for projections
    pub refine_args: RefineArgs,
    pub def_id: DefId,
}

pub type RefineArgs = List<Expr>;

/// A type constructor meant to be used as generic a argument of [kind base]. This is just an alias
/// to [`Binder<SubsetTy>`], but we expect the binder to have a single bound variable of the sort of
/// the underlying [base type].
///
/// [kind base]: GenericParamDefKind::Base
/// [base type]: SubsetTy::bty
pub type SubsetTyCtor = Binder<SubsetTy>;

impl SubsetTyCtor {
    pub fn as_bty_skipping_binder(&self) -> &BaseTy {
        &self.as_ref().skip_binder().bty
    }

    pub fn to_ty(&self) -> Ty {
        let sort = self.sort();
        if sort.is_unit() {
            self.replace_bound_reft(&Expr::unit()).to_ty()
        } else if let Some(def_id) = sort.is_unit_adt() {
            self.replace_bound_reft(&Expr::unit_adt(def_id)).to_ty()
        } else {
            Ty::exists(self.as_ref().map(SubsetTy::to_ty))
        }
    }
}

/// A subset type is a simplified version of a type that has the form `{b[e] | p}` where `b` is a
/// [`BaseTy`], `e` a refinement index, and `p` a predicate.
///
/// These are mainly found under a [`Binder`] with a single variable of the base type's sort. This
/// can be interpreted as a type constructor or an existial type. For example, under a binder with a
/// variable `v` of sort `int`, we can interpret `{i32[v] | v > 0}` as a lambda `λv:int. {i32[v] | v > 0}`
/// that "constructs" types when applied to ints, or as an existential type `∃v:int. {i32[v] | v > 0}`.
/// This second interpretation is the reason we call this a subset type, i.e., the type `∃v. {b[v] | p}`
/// corresponds to the subset of values of (base) type `b` whose index satisfies `p`. In other words,
/// these are the types written as `B{v: p}` in the surface syntax and correspond to the types
/// supported in other refinement type systems like Liquid Haskell (with the difference that we are
/// explicit about separating refinements from program values via an index).
///
/// The main purpose for subset types is to be used as generic arguments of [kind base] when
/// interpreted as type constructors. A subset type has two key properties that makes them suitable
/// for that.
///
/// First, because subset types are syntactically restricted, they make it easier to relate types
/// structurally (e.g., for subtyping). For instance, given two types `S<λv. T1>` and `S<λ. T2>`,
/// since we know `T1` and `T2` must be subset types, we also know they match structurally
/// (at least shallowly). The syntactic restriction also rules out more complex types like
/// `S<λv. (i32[v], i32[0])>` which simplifies some operations on types.
///
/// Second, subset types can be eagerly canonicalized via [*strengthening*] during substitution. For
/// example, suppose we have a function:
/// ```text
/// fn foo<T>(x: T[@a], y: { T[@b] | b == a }) { }
/// ```
/// If we instantiate `T` with `λv. { i32[v] | v > 0}`, after substitution and applying the lambda
/// (the indexing syntax `T[a]` corresponds to an application of the lambda), we get:
/// ```text
/// fn foo(x: {i32[@a] | a > 0}, y: { { i32[@b] | b > 0 } | b == a }) { }
/// ```
/// Via *strengthening* we can canonicalize this to
/// ```text
/// fn foo(x: {i32[@a] | a > 0}, y: { i32[@b] | b == a && b > 0 }) { }
/// ```
/// As a result, we can guarantee the syntactic restriction through substitution.
///
/// [kind base]: GenericParamDefKind::Base
/// [*strengthening*]: https://arxiv.org/pdf/2010.07763.pdf
#[derive(PartialEq, Clone, Eq, Hash, TyEncodable, TyDecodable)]
pub struct SubsetTy {
    /// **NOTE:** This [`BaseTy`] is mainly going to be under a [`Binder`]. It is not yet clear whether
    /// this [`BaseTy`] should be able to mention variables in the binder. In general, in a type
    /// `∃v. {b[e] | p}`, it's fine to mention `v` inside `b`, but since [`SubsetTy`] is meant to
    /// facilitate syntactic manipulation we may restrict this.
    pub bty: BaseTy,
    /// This can be an arbitrary expression which makes manipulation easier, but since this is mostly
    /// going to be under a binder we expect it to be [`Expr::nu()`].
    pub idx: Expr,
    pub pred: Expr,
}

impl SubsetTy {
    pub fn new(bty: BaseTy, idx: impl Into<Expr>, pred: impl Into<Expr>) -> Self {
        Self { bty, idx: idx.into(), pred: pred.into() }
    }

    pub fn trivial(bty: BaseTy, idx: impl Into<Expr>) -> Self {
        Self::new(bty, idx, Expr::tt())
    }

    pub fn strengthen(&self, pred: impl Into<Expr>) -> Self {
        let this = self.clone();
        Self { bty: this.bty, idx: this.idx, pred: Expr::and(this.pred, pred.into()) }
    }

    fn to_ty(&self) -> Ty {
        let bty = self.bty.clone();
        if self.pred.is_trivially_true() {
            Ty::indexed(bty, &self.idx)
        } else {
            Ty::constr(&self.pred, Ty::indexed(bty, &self.idx))
        }
    }
}

impl<'tcx> ToRustc<'tcx> for SubsetTy {
    type T = rustc_middle::ty::Ty<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> rustc_middle::ty::Ty<'tcx> {
        self.bty.to_rustc(tcx)
    }
}

#[derive(PartialEq, Clone, Eq, Hash, TyEncodable, TyDecodable)]
pub enum GenericArg {
    Ty(Ty),
    Base(SubsetTyCtor),
    Lifetime(Region),
    Const(Const),
}

impl GenericArg {
    pub fn expect_type(&self) -> &Ty {
        if let GenericArg::Ty(ty) = self {
            ty
        } else {
            bug!("expected `rty::GenericArg::Ty`, found `{self:?}`")
        }
    }

    pub fn expect_base(&self) -> &SubsetTyCtor {
        if let GenericArg::Base(ctor) = self {
            ctor
        } else {
            bug!("expected `rty::GenericArg::Base`, found `{self:?}`")
        }
    }

    pub fn from_param_def(param: &GenericParamDef) -> Self {
        match param.kind {
            GenericParamDefKind::Type { .. } => {
                let param_ty = ParamTy { index: param.index, name: param.name };
                GenericArg::Ty(Ty::param(param_ty))
            }
            GenericParamDefKind::Base => {
                // λv. T[v]
                let param_ty = ParamTy { index: param.index, name: param.name };
                GenericArg::Base(Binder::bind_with_sort(
                    SubsetTy::trivial(BaseTy::Param(param_ty), Expr::nu()),
                    Sort::Param(param_ty),
                ))
            }
            GenericParamDefKind::Lifetime => {
                let region = EarlyParamRegion { index: param.index, name: param.name };
                GenericArg::Lifetime(Region::ReEarlyParam(region))
            }
            GenericParamDefKind::Const { .. } => {
                let param_const = ParamConst { index: param.index, name: param.name };
                let kind = ConstKind::Param(param_const);
                GenericArg::Const(Const { kind })
            }
        }
    }

    /// Creates a `GenericArgs` from the definition of generic parameters, by calling a closure to
    /// obtain arg. The closures get to observe the `GenericArgs` as they're being built, which can
    /// be used to correctly replace defaults of generic parameters.
    pub fn for_item<F>(genv: GlobalEnv, def_id: DefId, mut mk_kind: F) -> QueryResult<GenericArgs>
    where
        F: FnMut(&GenericParamDef, &[GenericArg]) -> GenericArg,
    {
        let defs = genv.generics_of(def_id)?;
        let count = defs.count();
        let mut args = Vec::with_capacity(count);
        Self::fill_item(genv, &mut args, &defs, &mut mk_kind)?;
        Ok(List::from_vec(args))
    }

    pub fn identity_for_item(
        genv: GlobalEnv,
        def_id: impl Into<DefId>,
    ) -> QueryResult<GenericArgs> {
        Self::for_item(genv, def_id.into(), |param, _| GenericArg::from_param_def(param))
    }

    fn fill_item<F>(
        genv: GlobalEnv,
        args: &mut Vec<GenericArg>,
        generics: &Generics,
        mk_kind: &mut F,
    ) -> QueryResult<()>
    where
        F: FnMut(&GenericParamDef, &[GenericArg]) -> GenericArg,
    {
        if let Some(def_id) = generics.parent {
            let parent_generics = genv.generics_of(def_id)?;
            Self::fill_item(genv, args, &parent_generics, mk_kind)?;
        }
        for param in &generics.own_params {
            let kind = mk_kind(param, args);
            assert_eq!(param.index as usize, args.len(), "{args:#?}, {generics:#?}");
            args.push(kind);
        }
        Ok(())
    }
}

impl<'tcx> ToRustc<'tcx> for GenericArg {
    type T = rustc_middle::ty::GenericArg<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        use rustc_middle::ty;
        match self {
            GenericArg::Ty(ty) => ty::GenericArg::from(ty.to_rustc(tcx)),
            GenericArg::Base(ctor) => ty::GenericArg::from(ctor.skip_binder_ref().to_rustc(tcx)),
            GenericArg::Lifetime(re) => ty::GenericArg::from(re.to_rustc(tcx)),
            GenericArg::Const(c) => ty::GenericArg::from(c.to_rustc(tcx)),
        }
    }
}

pub type GenericArgs = List<GenericArg>;

#[extension(pub trait GenericArgsExt)]
impl GenericArgs {
    #[track_caller]
    fn box_args(&self) -> (&Ty, &Ty) {
        if let [GenericArg::Ty(deref), GenericArg::Ty(alloc)] = &self[..] {
            (deref, alloc)
        } else {
            bug!("invalid generic arguments for box");
        }
    }

    // We can't implement [`ToRustc`] because of coherence so we add it here
    fn to_rustc<'tcx>(&self, tcx: TyCtxt<'tcx>) -> rustc_middle::ty::GenericArgsRef<'tcx> {
        tcx.mk_args_from_iter(self.iter().map(|arg| arg.to_rustc(tcx)))
    }
}

impl Clause {
    pub fn new(vars: impl Into<List<BoundVariableKind>>, kind: ClauseKind) -> Self {
        Clause { kind: Binder::bind_with_vars(kind, vars.into()) }
    }

    pub fn kind(&self) -> Binder<ClauseKind> {
        self.kind.clone()
    }

    // FIXME(nilehmann) we should deal with the binder in all the places this is used instead of
    // blindly skipping it here
    pub fn kind_skipping_binder(&self) -> ClauseKind {
        self.kind.clone().skip_binder()
    }
}

impl From<Binder<ClauseKind>> for Clause {
    fn from(kind: Binder<ClauseKind>) -> Self {
        Clause { kind }
    }
}

impl CoroutineObligPredicate {
    pub fn to_poly_fn_sig(&self) -> PolyFnSig {
        let vars = vec![];

        let resume_ty = &self.resume_ty;
        let env_ty = Ty::coroutine(self.def_id, resume_ty.clone(), self.upvar_tys.clone());

        let inputs = List::from_arr([env_ty, resume_ty.clone()]);
        let output =
            Binder::bind_with_vars(FnOutput::new(self.output.clone(), vec![]), List::empty());

        PolyFnSig::bind_with_vars(
            FnSig::new(Safety::Safe, abi::Abi::RustCall, List::empty(), inputs, output),
            List::from(vars),
        )
    }
}

impl RefinementGenerics {
    pub fn count(&self) -> usize {
        self.parent_count + self.params.len()
    }

    pub fn param_at(&self, param_index: usize, genv: GlobalEnv) -> QueryResult<RefineParam> {
        if let Some(index) = param_index.checked_sub(self.parent_count) {
            Ok(self.params[index].clone())
        } else {
            let parent = self.parent.expect("parent_count > 0 but no parent?");
            genv.refinement_generics_of(parent)?
                .param_at(param_index, genv)
        }
    }

    /// Iterate and collect all parameters in this item including parents
    pub fn collect_all_params<T, S>(
        &self,
        genv: GlobalEnv,
        mut f: impl FnMut(RefineParam) -> T,
    ) -> QueryResult<S>
    where
        S: FromIterator<T>,
    {
        (0..self.count())
            .map(|i| Ok(f(self.param_at(i, genv)?)))
            .try_collect()
    }
}

impl EarlyBinder<GenericPredicates> {
    pub fn predicates(&self) -> EarlyBinder<List<Clause>> {
        EarlyBinder(self.0.predicates.clone())
    }
}

impl EarlyBinder<FuncSort> {
    /// See [`subst::GenericsSubstForSort`]
    pub fn instantiate_func_sort<E>(
        self,
        sort_for_param: impl FnMut(ParamTy) -> Result<Sort, E>,
    ) -> Result<FuncSort, E> {
        self.0.try_fold_with(&mut subst::GenericsSubstFolder::new(
            subst::GenericsSubstForSort { sort_for_param },
            &[],
        ))
    }
}

impl VariantSig {
    pub fn new(adt_def: AdtDef, args: GenericArgs, fields: List<Ty>, idx: Expr) -> Self {
        VariantSig { adt_def, args, fields, idx }
    }

    pub fn fields(&self) -> &[Ty] {
        &self.fields
    }

    pub fn ret(&self) -> Ty {
        let bty = BaseTy::Adt(self.adt_def.clone(), self.args.clone());
        Ty::indexed(bty, self.idx.clone())
    }
}

impl FnSig {
    pub fn new(
        safety: Safety,
        abi: abi::Abi,
        requires: List<Expr>,
        inputs: List<Ty>,
        output: Binder<FnOutput>,
    ) -> Self {
        FnSig { safety, abi, requires, inputs, output }
    }

    pub fn requires(&self) -> &[Expr] {
        &self.requires
    }

    pub fn inputs(&self) -> &[Ty] {
        &self.inputs
    }

    pub fn output(&self) -> &Binder<FnOutput> {
        &self.output
    }
}

impl<'tcx> ToRustc<'tcx> for FnSig {
    type T = rustc_middle::ty::FnSig<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        tcx.mk_fn_sig(
            self.inputs().iter().map(|ty| ty.to_rustc(tcx)),
            self.output().as_ref().skip_binder().to_rustc(tcx),
            false,
            self.safety,
            self.abi,
        )
    }
}

impl FnOutput {
    pub fn new(ret: Ty, ensures: impl Into<List<Ensures>>) -> Self {
        Self { ret, ensures: ensures.into() }
    }
}

impl<'tcx> ToRustc<'tcx> for FnOutput {
    type T = rustc_middle::ty::Ty<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        self.ret.to_rustc(tcx)
    }
}

impl AdtDef {
    pub fn new(
        rustc: ty::AdtDef,
        sort_def: AdtSortDef,
        invariants: Vec<Invariant>,
        opaque: bool,
    ) -> Self {
        AdtDef(Interned::new(AdtDefData { invariants, sort_def, opaque, rustc }))
    }

    pub fn did(&self) -> DefId {
        self.0.rustc.did()
    }

    pub fn sort_def(&self) -> &AdtSortDef {
        &self.0.sort_def
    }

    pub fn sort(&self, args: &[GenericArg]) -> Sort {
        self.sort_def().sort(args)
    }

    pub fn is_box(&self) -> bool {
        self.0.rustc.is_box()
    }

    pub fn is_enum(&self) -> bool {
        self.0.rustc.is_enum()
    }

    pub fn is_struct(&self) -> bool {
        self.0.rustc.is_struct()
    }

    pub fn variants(&self) -> &IndexSlice<VariantIdx, VariantDef> {
        self.0.rustc.variants()
    }

    pub fn variant(&self, idx: VariantIdx) -> &VariantDef {
        self.0.rustc.variant(idx)
    }

    pub fn invariants(&self) -> &[Invariant] {
        &self.0.invariants
    }

    pub fn discriminants(&self) -> impl Iterator<Item = (VariantIdx, u128)> + '_ {
        self.0.rustc.discriminants()
    }

    pub fn is_opaque(&self) -> bool {
        self.0.opaque
    }
}

impl<T> Opaqueness<T> {
    pub fn map<S>(self, f: impl FnOnce(T) -> S) -> Opaqueness<S> {
        match self {
            Opaqueness::Opaque => Opaqueness::Opaque,
            Opaqueness::Transparent(value) => Opaqueness::Transparent(f(value)),
        }
    }

    pub fn as_ref(&self) -> Opaqueness<&T> {
        match self {
            Opaqueness::Opaque => Opaqueness::Opaque,
            Opaqueness::Transparent(value) => Opaqueness::Transparent(value),
        }
    }

    pub fn as_deref(&self) -> Opaqueness<&T::Target>
    where
        T: std::ops::Deref,
    {
        match self {
            Opaqueness::Opaque => Opaqueness::Opaque,
            Opaqueness::Transparent(value) => Opaqueness::Transparent(value.deref()),
        }
    }

    pub fn ok_or_else<E>(self, err: impl FnOnce() -> E) -> Result<T, E> {
        match self {
            Opaqueness::Transparent(v) => Ok(v),
            Opaqueness::Opaque => Err(err()),
        }
    }

    #[track_caller]
    pub fn expect(self, msg: &str) -> T {
        match self {
            Opaqueness::Transparent(val) => val,
            Opaqueness::Opaque => bug!("{}", msg),
        }
    }
}

impl<T, E> Opaqueness<Result<T, E>> {
    pub fn transpose(self) -> Result<Opaqueness<T>, E> {
        match self {
            Opaqueness::Transparent(Ok(x)) => Ok(Opaqueness::Transparent(x)),
            Opaqueness::Transparent(Err(e)) => Err(e),
            Opaqueness::Opaque => Ok(Opaqueness::Opaque),
        }
    }
}

impl EarlyBinder<PolyVariant> {
    pub fn to_poly_fn_sig(&self) -> EarlyBinder<PolyFnSig> {
        self.as_ref().map(|poly_variant| {
            poly_variant.as_ref().map(|variant| {
                let ret = variant.ret().shift_in_escaping(1);
                let output = Binder::bind_with_vars(FnOutput::new(ret, vec![]), List::empty());
                FnSig::new(
                    Safety::Safe,
                    abi::Abi::Rust,
                    List::empty(),
                    variant.fields.clone(),
                    output,
                )
            })
        })
    }
}

impl TyKind {
    fn intern(self) -> Ty {
        Ty(Interned::new(self))
    }
}

impl AliasTy {
    pub fn new(def_id: DefId, args: GenericArgs, refine_args: RefineArgs) -> Self {
        AliasTy { args, refine_args, def_id }
    }

    /// This method work only with associated type projections (i.e., no opaque tpes)
    pub fn self_ty(&self) -> &Ty {
        self.args[0].expect_type()
    }
}

impl<'tcx> ToRustc<'tcx> for AliasTy {
    type T = rustc_middle::ty::AliasTy<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        rustc_middle::ty::AliasTy::new(tcx, self.def_id, self.args.to_rustc(tcx))
    }
}

impl Binder<Expr> {
    /// See [`Expr::is_trivially_true`]
    pub fn is_trivially_true(&self) -> bool {
        self.skip_binder_ref().is_trivially_true()
    }
}

fn uint_invariants(uint_ty: UintTy, overflow_checking: bool) -> &'static [Invariant] {
    static DEFAULT: LazyLock<[Invariant; 1]> = LazyLock::new(|| {
        [Invariant { pred: Binder::bind_with_sort(Expr::ge(Expr::nu(), Expr::zero()), Sort::Int) }]
    });

    static OVERFLOW: LazyLock<UnordMap<UintTy, [Invariant; 2]>> = LazyLock::new(|| {
        UINT_TYS
            .into_iter()
            .map(|uint_ty| {
                let invariants = [
                    Invariant {
                        pred: Binder::bind_with_sort(Expr::ge(Expr::nu(), Expr::zero()), Sort::Int),
                    },
                    Invariant {
                        pred: Binder::bind_with_sort(
                            Expr::le(Expr::nu(), Expr::uint_max(uint_ty)),
                            Sort::Int,
                        ),
                    },
                ];
                (uint_ty, invariants)
            })
            .collect()
    });
    if overflow_checking {
        &OVERFLOW[&uint_ty]
    } else {
        &*DEFAULT
    }
}

fn int_invariants(int_ty: IntTy, overflow_checking: bool) -> &'static [Invariant] {
    static DEFAULT: [Invariant; 0] = [];

    static OVERFLOW: LazyLock<UnordMap<IntTy, [Invariant; 2]>> = LazyLock::new(|| {
        INT_TYS
            .into_iter()
            .map(|int_ty| {
                let invariants = [
                    Invariant {
                        pred: Binder::bind_with_sort(
                            Expr::ge(Expr::nu(), Expr::int_min(int_ty)),
                            Sort::Int,
                        ),
                    },
                    Invariant {
                        pred: Binder::bind_with_sort(
                            Expr::le(Expr::nu(), Expr::int_max(int_ty)),
                            Sort::Int,
                        ),
                    },
                ];
                (int_ty, invariants)
            })
            .collect()
    });
    if overflow_checking {
        &OVERFLOW[&int_ty]
    } else {
        &DEFAULT
    }
}

impl_internable!(AdtDefData, AdtSortDefData, TyKind);
impl_slice_internable!(
    Ty,
    GenericArg,
    Ensures,
    InferMode,
    Sort,
    GenericParamDef,
    TraitRef,
    Binder<ExistentialPredicate>,
    Clause,
    PolyVariant,
    Invariant,
    RefineParam,
    AssocRefinement,
    SortParamKind,
);

#[macro_export]
macro_rules! _Int {
    ($int_ty:pat, $idxs:pat) => {
        TyKind::Indexed(BaseTy::Int($int_ty), $idxs)
    };
}
pub use crate::_Int as Int;

#[macro_export]
macro_rules! _Uint {
    ($uint_ty:pat, $idxs:pat) => {
        TyKind::Indexed(BaseTy::Uint($uint_ty), $idxs)
    };
}
pub use crate::_Uint as Uint;

#[macro_export]
macro_rules! _Bool {
    ($idxs:pat) => {
        TyKind::Indexed(BaseTy::Bool, $idxs)
    };
}
pub use crate::_Bool as Bool;

#[macro_export]
macro_rules! _Ref {
    ($($pats:pat),+ $(,)?) => {
        $crate::rty::TyKind::Indexed($crate::rty::BaseTy::Ref($($pats),+), _)
    };
}
pub use crate::_Ref as Ref;

pub struct WfckResults {
    pub owner: FluxOwnerId,
    record_ctors: ItemLocalMap<DefId>,
    node_sorts: ItemLocalMap<Sort>,
    bin_rel_sorts: ItemLocalMap<Sort>,
    coercions: ItemLocalMap<Vec<Coercion>>,
}

#[derive(Debug)]
pub enum Coercion {
    Inject(DefId),
    Project(DefId),
}

pub type ItemLocalMap<T> = UnordMap<fhir::ItemLocalId, T>;

#[derive(Debug)]
pub struct LocalTableInContext<'a, T> {
    owner: FluxOwnerId,
    data: &'a ItemLocalMap<T>,
}

pub struct LocalTableInContextMut<'a, T> {
    owner: FluxOwnerId,
    data: &'a mut ItemLocalMap<T>,
}

impl WfckResults {
    pub fn new(owner: impl Into<FluxOwnerId>) -> Self {
        Self {
            owner: owner.into(),
            record_ctors: ItemLocalMap::default(),
            node_sorts: ItemLocalMap::default(),
            bin_rel_sorts: ItemLocalMap::default(),
            coercions: ItemLocalMap::default(),
        }
    }

    pub fn record_ctors_mut(&mut self) -> LocalTableInContextMut<DefId> {
        LocalTableInContextMut { owner: self.owner, data: &mut self.record_ctors }
    }

    pub fn record_ctors(&self) -> LocalTableInContext<DefId> {
        LocalTableInContext { owner: self.owner, data: &self.record_ctors }
    }

    pub fn node_sorts_mut(&mut self) -> LocalTableInContextMut<Sort> {
        LocalTableInContextMut { owner: self.owner, data: &mut self.node_sorts }
    }

    pub fn node_sorts(&self) -> LocalTableInContext<Sort> {
        LocalTableInContext { owner: self.owner, data: &self.node_sorts }
    }

    pub fn bin_rel_sorts_mut(&mut self) -> LocalTableInContextMut<Sort> {
        LocalTableInContextMut { owner: self.owner, data: &mut self.bin_rel_sorts }
    }

    pub fn bin_rel_sorts(&self) -> LocalTableInContext<Sort> {
        LocalTableInContext { owner: self.owner, data: &self.bin_rel_sorts }
    }

    pub fn coercions_mut(&mut self) -> LocalTableInContextMut<Vec<Coercion>> {
        LocalTableInContextMut { owner: self.owner, data: &mut self.coercions }
    }

    pub fn coercions(&self) -> LocalTableInContext<Vec<Coercion>> {
        LocalTableInContext { owner: self.owner, data: &self.coercions }
    }
}

impl<'a, T> LocalTableInContextMut<'a, T> {
    pub fn insert(&mut self, fhir_id: FhirId, value: T) {
        assert_eq!(self.owner, fhir_id.owner);
        self.data.insert(fhir_id.local_id, value);
    }
}

impl<'a, T> LocalTableInContext<'a, T> {
    pub fn get(&self, fhir_id: FhirId) -> Option<&'a T> {
        assert_eq!(self.owner, fhir_id.owner);
        self.data.get(&fhir_id.local_id)
    }
}
