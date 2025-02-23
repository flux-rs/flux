//! Defines how flux represents refinement types internally. Definitions in this module are used
//! during refinement type checking. A couple of important differences between definitions in this
//! module and in [`crate::fhir`] are:
//!
//! * Types in this module use debruijn indices to represent local binders.
//! * Data structures are interned so they can be cheaply cloned.

mod binder;
pub mod canonicalize;
mod expr;
pub mod fold;
pub(crate) mod normalize;
mod pretty;
pub mod refining;
pub mod region_matching;
pub mod subst;
use std::{borrow::Cow, cmp::Ordering, hash::Hash, sync::LazyLock};

pub use binder::{Binder, BoundReftKind, BoundVariableKind, BoundVariableKinds, EarlyBinder};
pub use expr::{
    AggregateKind, AliasReft, BinOp, BoundReft, Constant, Ctor, ESpan, EVid, EarlyReftParam, Expr,
    ExprKind, FieldProj, HoleKind, KVar, KVid, Lambda, Loc, Name, Path, Real, UnOp, Var,
};
pub use flux_arc_interner::List;
use flux_arc_interner::{impl_internable, impl_slice_internable, Interned};
use flux_common::{bug, tracked_span_assert_eq, tracked_span_bug};
use flux_macros::{TypeFoldable, TypeVisitable};
pub use flux_rustc_bridge::ty::{
    AliasKind, BoundRegion, BoundRegionKind, BoundVar, Const, ConstKind, ConstVid, DebruijnIndex,
    EarlyParamRegion, LateParamRegion, LateParamRegionKind,
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
use refining::{Refine as _, Refiner};
use rustc_data_structures::{fx::FxIndexMap, unord::UnordMap};
use rustc_hir::{
    def_id::{DefId, DefIndex},
    LangItem, Safety,
};
use rustc_index::{newtype_index, IndexSlice};
use rustc_macros::{extension, Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_middle::ty::TyCtxt;
pub use rustc_middle::{
    mir::Mutability,
    ty::{AdtFlags, ClosureKind, FloatTy, IntTy, ParamConst, ParamTy, ScalarInt, UintTy},
};
use rustc_span::{sym, symbol::kw, Symbol};
pub use rustc_target::abi::{VariantIdx, FIRST_VARIANT};
use rustc_target::spec::abi;
use rustc_type_ir::Upcast as _;
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

/// The definition of the data sort automatically generated for a struct or enum.
#[derive(Debug, Clone, Eq, PartialEq, Hash, TyEncodable, TyDecodable)]
pub struct AdtSortDef(Interned<AdtSortDefData>);

#[derive(Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct AdtSortVariant {
    /// The list of field names as declared in the `#[flux::refined_by(...)]` annotation
    field_names: Vec<Symbol>,
    /// The sort of each of the fields. Note that these can contain [sort variables]. Methods used
    /// to access these sorts guarantee they are properly instantiated.
    ///
    /// [sort variables]: Sort::Var
    sorts: List<Sort>,
}

impl AdtSortVariant {
    pub fn new(fields: Vec<(Symbol, Sort)>) -> Self {
        let (field_names, sorts) = fields.into_iter().unzip();
        AdtSortVariant { field_names, sorts: List::from_vec(sorts) }
    }

    pub fn fields(&self) -> usize {
        self.sorts.len()
    }

    pub fn field_names(&self) -> &Vec<Symbol> {
        &self.field_names
    }

    pub fn sort_by_field_name(&self, args: &[Sort]) -> FxIndexMap<Symbol, Sort> {
        std::iter::zip(&self.field_names, &self.sorts.fold_with(&mut SortSubst::new(args)))
            .map(|(name, sort)| (*name, sort.clone()))
            .collect()
    }

    pub fn field_by_name(
        &self,
        def_id: DefId,
        args: &[Sort],
        name: Symbol,
    ) -> Option<(FieldProj, Sort)> {
        let idx = self.field_names.iter().position(|it| name == *it)?;
        let proj = FieldProj::Adt { def_id, field: idx as u32 };
        let sort = self.sorts[idx].fold_with(&mut SortSubst::new(args));
        Some((proj, sort))
    }

    pub fn field_sorts(&self, args: &[Sort]) -> List<Sort> {
        self.sorts.fold_with(&mut SortSubst::new(args))
    }
}

#[derive(Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
struct AdtSortDefData {
    /// [`DefId`] of the struct or enum this data sort is associated to.
    def_id: DefId,
    /// The list of the type parameters used in the `#[flux::refined_by(..)]` annotation.
    ///
    /// See [`fhir::RefinedBy::sort_params`] for more details. This is a version of that but using
    /// [`ParamTy`] instead of [`DefId`].
    ///
    /// The length of this list corresponds to the number of sort variables bound by this definition.
    params: Vec<ParamTy>,
    // The `index` is *either* the user defined indices or the "reflected" ADT
    // kind: RefinementKind,
    /// A vec of variants of the ADT;
    /// - a `struct` sort -- used for types with a `refined_by` has a single variant;
    /// - a `reflected` sort -- used for `reflected` enums have multiple variants
    variants: Vec<AdtSortVariant>,
    is_reflected: bool,
    is_struct: bool,
}

impl AdtSortDef {
    pub fn new(
        def_id: DefId,
        params: Vec<ParamTy>,
        variants: Vec<AdtSortVariant>,
        is_reflected: bool,
        is_struct: bool,
    ) -> Self {
        Self(Interned::new(AdtSortDefData { def_id, params, variants, is_reflected, is_struct }))
    }

    pub fn did(&self) -> DefId {
        self.0.def_id
    }

    pub fn struct_variant(&self) -> &AdtSortVariant {
        tracked_span_assert_eq!(self.0.is_struct, true);
        &self.0.variants[0]
    }

    pub fn is_reflected(&self) -> bool {
        self.0.is_reflected
    }

    pub fn is_struct(&self) -> bool {
        self.0.is_struct
    }

    pub fn non_enum_fields(&self) -> usize {
        self.struct_variant().sorts.len()
    }

    pub fn projections(&self) -> impl Iterator<Item = FieldProj> + '_ {
        (0..self.struct_variant().fields())
            .map(|i| FieldProj::Adt { def_id: self.did(), field: i as u32 })
    }

    pub fn field_names(&self) -> &[Symbol] {
        &self.struct_variant().field_names[..]
    }

    pub fn sort_by_field_name(&self, args: &[Sort]) -> FxIndexMap<Symbol, Sort> {
        self.struct_variant().sort_by_field_name(args)
    }

    pub fn field_by_name(&self, args: &[Sort], name: Symbol) -> Option<(FieldProj, Sort)> {
        self.struct_variant().field_by_name(self.did(), args, name)
    }

    pub fn field_sorts(&self, args: &[Sort]) -> List<Sort> {
        self.struct_variant().field_sorts(args)
    }

    pub fn to_sort(&self, args: &[GenericArg]) -> Sort {
        let sorts = self
            .filter_generic_args(args)
            .map(|arg| arg.expect_base().sort())
            .collect();

        Sort::App(SortCtor::Adt(self.clone()), sorts)
    }

    /// Given a list of generic args, returns an iterator of the generic arguments that should be
    /// mapped to sorts for instantiation.
    pub fn filter_generic_args<'a, A>(&'a self, args: &'a [A]) -> impl Iterator<Item = &'a A> + 'a {
        self.0.params.iter().map(|p| &args[p.index as usize])
    }

    pub fn identity_args(&self) -> List<Sort> {
        (0..self.0.params.len())
            .map(|i| Sort::Var(ParamSort::from(i)))
            .collect()
    }

    /// Gives the number of sort variables bound by this definition.
    pub fn param_count(&self) -> usize {
        self.0.params.len()
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
                    GenericParamDefKind::Type { has_default }
                    | GenericParamDefKind::Const { has_default }
                    | GenericParamDefKind::Base { has_default } => has_default,
                    GenericParamDefKind::Lifetime => false,
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
    pub own_params: List<RefineParam>,
}

#[derive(
    PartialEq, Eq, Debug, Clone, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
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
    Base { has_default: bool },
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

impl Clause {
    pub fn new(vars: impl Into<List<BoundVariableKind>>, kind: ClauseKind) -> Self {
        Clause { kind: Binder::bind_with_vars(kind, vars.into()) }
    }

    pub fn kind(&self) -> Binder<ClauseKind> {
        self.kind.clone()
    }

    fn as_trait_clause(&self) -> Option<Binder<TraitPredicate>> {
        let clause = self.kind();
        if let ClauseKind::Trait(trait_clause) = clause.skip_binder_ref() {
            Some(clause.rebind(trait_clause.clone()))
        } else {
            None
        }
    }

    pub fn as_projection_clause(&self) -> Option<Binder<ProjectionPredicate>> {
        let clause = self.kind();
        if let ClauseKind::Projection(proj_clause) = clause.skip_binder_ref() {
            Some(clause.rebind(proj_clause.clone()))
        } else {
            None
        }
    }

    // FIXME(nilehmann) we should deal with the binder in all the places this is used instead of
    // blindly skipping it here
    pub fn kind_skipping_binder(&self) -> ClauseKind {
        self.kind.clone().skip_binder()
    }

    /// Group `Fn` trait clauses with their corresponding `FnOnce::Output` projection
    /// predicate. This assumes there's exactly one corresponding projection predicate and will
    /// crash otherwise.
    pub fn split_off_fn_trait_clauses(
        genv: GlobalEnv,
        clauses: &Clauses,
    ) -> (Vec<Clause>, Vec<Binder<FnTraitPredicate>>) {
        let mut fn_trait_clauses = vec![];
        let mut fn_trait_output_clauses = vec![];
        let mut rest = vec![];
        for clause in clauses {
            if let Some(trait_clause) = clause.as_trait_clause()
                && let Some(kind) = genv.tcx().fn_trait_kind_from_def_id(trait_clause.def_id())
            {
                fn_trait_clauses.push((kind, trait_clause));
            } else if let Some(proj_clause) = clause.as_projection_clause()
                && genv.is_fn_once_output(proj_clause.projection_def_id())
            {
                fn_trait_output_clauses.push(proj_clause);
            } else {
                rest.push(clause.clone());
            }
        }

        let fn_trait_clauses = fn_trait_clauses
            .into_iter()
            .map(|(kind, fn_trait_clause)| {
                let mut candidates = vec![];
                for fn_trait_output_clause in &fn_trait_output_clauses {
                    if fn_trait_output_clause.self_ty() == fn_trait_clause.self_ty() {
                        candidates.push(fn_trait_output_clause.clone());
                    }
                }
                tracked_span_assert_eq!(candidates.len(), 1);
                let proj_pred = candidates.pop().unwrap().skip_binder();
                fn_trait_clause.map(|fn_trait_clause| {
                    FnTraitPredicate {
                        kind,
                        self_ty: fn_trait_clause.self_ty().to_ty(),
                        tupled_args: fn_trait_clause.trait_ref.args[1].expect_base().to_ty(),
                        output: proj_pred.term.to_ty(),
                    }
                })
            })
            .collect_vec();
        (rest, fn_trait_clauses)
    }
}

impl<'tcx> ToRustc<'tcx> for Clause {
    type T = rustc_middle::ty::Clause<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        self.kind.to_rustc(tcx).upcast(tcx)
    }
}

impl From<Binder<ClauseKind>> for Clause {
    fn from(kind: Binder<ClauseKind>) -> Self {
        Clause { kind }
    }
}

pub type Clauses = List<Clause>;

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub enum ClauseKind {
    Trait(TraitPredicate),
    Projection(ProjectionPredicate),
    RegionOutlives(RegionOutlivesPredicate),
    TypeOutlives(TypeOutlivesPredicate),
    ConstArgHasType(Const, Ty),
}

impl<'tcx> ToRustc<'tcx> for ClauseKind {
    type T = rustc_middle::ty::ClauseKind<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        match self {
            ClauseKind::Trait(trait_predicate) => {
                rustc_middle::ty::ClauseKind::Trait(trait_predicate.to_rustc(tcx))
            }
            ClauseKind::Projection(projection_predicate) => {
                rustc_middle::ty::ClauseKind::Projection(projection_predicate.to_rustc(tcx))
            }
            ClauseKind::RegionOutlives(outlives_predicate) => {
                rustc_middle::ty::ClauseKind::RegionOutlives(outlives_predicate.to_rustc(tcx))
            }
            ClauseKind::TypeOutlives(outlives_predicate) => {
                rustc_middle::ty::ClauseKind::TypeOutlives(outlives_predicate.to_rustc(tcx))
            }
            ClauseKind::ConstArgHasType(constant, ty) => {
                rustc_middle::ty::ClauseKind::ConstArgHasType(
                    constant.to_rustc(tcx),
                    ty.to_rustc(tcx),
                )
            }
        }
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Debug, TyEncodable, TyDecodable)]
pub struct OutlivesPredicate<T>(pub T, pub Region);

pub type TypeOutlivesPredicate = OutlivesPredicate<Ty>;
pub type RegionOutlivesPredicate = OutlivesPredicate<Region>;

impl<'tcx, V: ToRustc<'tcx>> ToRustc<'tcx> for OutlivesPredicate<V> {
    type T = rustc_middle::ty::OutlivesPredicate<'tcx, V::T>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        rustc_middle::ty::OutlivesPredicate(self.0.to_rustc(tcx), self.1.to_rustc(tcx))
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct TraitPredicate {
    pub trait_ref: TraitRef,
}

impl TraitPredicate {
    fn self_ty(&self) -> SubsetTyCtor {
        self.trait_ref.self_ty()
    }
}

impl<'tcx> ToRustc<'tcx> for TraitPredicate {
    type T = rustc_middle::ty::TraitPredicate<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        rustc_middle::ty::TraitPredicate {
            polarity: rustc_middle::ty::PredicatePolarity::Positive,
            trait_ref: self.trait_ref.to_rustc(tcx),
        }
    }
}

pub type PolyTraitPredicate = Binder<TraitPredicate>;

impl PolyTraitPredicate {
    fn def_id(&self) -> DefId {
        self.skip_binder_ref().trait_ref.def_id
    }

    fn self_ty(&self) -> Binder<SubsetTyCtor> {
        self.clone().map(|predicate| predicate.self_ty())
    }
}

#[derive(
    Debug, Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct TraitRef {
    pub def_id: DefId,
    pub args: GenericArgs,
}

impl TraitRef {
    pub fn self_ty(&self) -> SubsetTyCtor {
        self.args[0].expect_base().clone()
    }
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
                        projection.term.skip_binder_ref().to_rustc(tcx).into(),
                    ),
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
    pub term: SubsetTyCtor,
}

#[derive(
    PartialEq, Eq, Hash, Debug, Clone, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct ProjectionPredicate {
    pub projection_ty: AliasTy,
    pub term: SubsetTyCtor,
}

impl ProjectionPredicate {
    pub fn self_ty(&self) -> SubsetTyCtor {
        self.projection_ty.self_ty().clone()
    }
}

impl<'tcx> ToRustc<'tcx> for ProjectionPredicate {
    type T = rustc_middle::ty::ProjectionPredicate<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        rustc_middle::ty::ProjectionPredicate {
            projection_term: rustc_middle::ty::AliasTerm::new_from_args(
                tcx,
                self.projection_ty.def_id,
                self.projection_ty.args.to_rustc(tcx),
            ),
            term: self.term.as_bty_skipping_binder().to_rustc(tcx).into(),
        }
    }
}

pub type PolyProjectionPredicate = Binder<ProjectionPredicate>;

impl PolyProjectionPredicate {
    fn projection_def_id(&self) -> DefId {
        self.skip_binder_ref().projection_ty.def_id
    }

    pub fn self_ty(&self) -> Binder<SubsetTyCtor> {
        self.clone().map(|predicate| predicate.self_ty())
    }
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

    pub fn to_closure_sig(
        &self,
        closure_id: DefId,
        tys: List<Ty>,
        args: &flux_rustc_bridge::ty::GenericArgs,
    ) -> PolyFnSig {
        let mut vars = vec![];

        let closure_ty = Ty::closure(closure_id, tys, args);
        let env_ty = match self.kind {
            ClosureKind::Fn => {
                vars.push(BoundVariableKind::Region(BoundRegionKind::ClosureEnv));
                let br = BoundRegion {
                    var: BoundVar::from_usize(vars.len() - 1),
                    kind: BoundRegionKind::ClosureEnv,
                };
                Ty::mk_ref(ReBound(INNERMOST, br), closure_ty, Mutability::Not)
            }
            ClosureKind::FnMut => {
                vars.push(BoundVariableKind::Region(BoundRegionKind::ClosureEnv));
                let br = BoundRegion {
                    var: BoundVar::from_usize(vars.len() - 1),
                    kind: BoundRegionKind::ClosureEnv,
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

/// An id for an associated refinement with a type-level invariant ensuring that it exists.
///
/// We represent the id as a container id and an arbitrary name. This doesn't guarantee the
/// existence of the associated refinement, so we must be careful when creating instances of
/// this struct.
///
/// We mark the struct as `non_exhaustive` to make it harder to create one by mistake without
/// calling [`AssocReftId::new`]. We also have a clippy lint disallowing [`AssocReftId::new`]
/// which can be disabled selectively when we can ensure the associated refinement exists.
///
/// The struct is generic on the container `Id` because we use it with various kinds of ids,
/// e.g., [`DefId`], [`MaybeExternId`], ...
#[derive(Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable, TypeVisitable, TypeFoldable)]
#[non_exhaustive]
pub struct AssocReftId<Id = DefId> {
    /// Id of the container, i.e., the impl block or trait.
    pub container_id: Id,
    /// Name of the associated refinement
    pub name: Symbol,
}

impl<Id> AssocReftId<Id> {
    pub fn new(container_id: Id, name: Symbol) -> Self {
        Self { container_id, name }
    }
}

impl AssocReftId {
    pub fn index(self) -> AssocReftId<DefIndex> {
        AssocReftId { container_id: self.container_id.index, name: self.name }
    }
}

#[derive(Clone, Encodable, Decodable)]
pub struct AssocRefinements {
    pub items: List<AssocReftId>,
}

impl Default for AssocRefinements {
    fn default() -> Self {
        Self { items: List::empty() }
    }
}

impl AssocRefinements {
    pub fn find(&self, name: Symbol) -> Option<AssocReftId> {
        self.items.iter().find(|it| it.name == name).copied()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum SortCtor {
    Set,
    Map,
    Adt(AdtSortDef),
    User { name: Symbol },
}

newtype_index! {
    /// [`ParamSort`] is used for polymorphic sorts (`Set`, `Map`, etc.) and [bit-vector size parameters].
    /// They should occur "bound" under a [`PolyFuncSort`] or an [`AdtSortDef`]. We assume there's a
    /// single binder and a [`ParamSort`] represents a variable as an index into the list of variables
    /// bound by that binder, i.e., the representation doesnt't support higher-ranked sorts.
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
    Char,
    Loc,
    Param(ParamTy),
    Tuple(List<Sort>),
    Alias(AliasKind, AliasTy),
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
            && sort_def.is_struct()
            && sort_def.non_enum_fields() == 0
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
pub enum ConstantInfo {
    /// An uninterpreted constant
    Uninterpreted,
    /// A non-integral constant whose value is specified by the user
    Interpreted(Expr, Sort),
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
    pub safety: Safety,
    pub abi: abi::Abi,
    pub requires: List<Expr>,
    pub inputs: List<Ty>,
    pub output: Binder<FnOutput>,
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

pub type TyCtor = Binder<Ty>;

impl TyCtor {
    pub fn to_ty(&self) -> Ty {
        match &self.vars()[..] {
            [] => {
                return self.skip_binder_ref().shift_out_escaping(1);
            }
            [BoundVariableKind::Refine(sort, ..)] => {
                if sort.is_unit() {
                    return self.replace_bound_reft(&Expr::unit());
                }
                if let Some(def_id) = sort.is_unit_adt() {
                    return self.replace_bound_reft(&Expr::unit_struct(def_id));
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

        let args = List::from_arr([GenericArg::Ty(deref_ty), GenericArg::Ty(alloc_ty)]);

        let bty = BaseTy::adt(adt_def, args);
        Ok(Ty::indexed(bty, Expr::unit_struct(def_id)))
    }

    pub fn mk_box_with_default_alloc(genv: GlobalEnv, deref_ty: Ty) -> QueryResult<Ty> {
        let def_id = genv.tcx().require_lang_item(LangItem::OwnedBox, None);

        let generics = genv.generics_of(def_id)?;
        let alloc_ty = genv
            .lower_type_of(generics.own_params[1].def_id)?
            .skip_binder()
            .refine(&Refiner::default_for_item(genv, def_id)?)?;

        Ty::mk_box(genv, deref_ty, alloc_ty)
    }

    pub fn tuple(tys: impl Into<List<Ty>>) -> Ty {
        BaseTy::Tuple(tys.into()).to_ty()
    }

    pub fn array(ty: Ty, c: Const) -> Ty {
        BaseTy::Array(ty, c).to_ty()
    }

    pub fn closure(
        did: DefId,
        tys: impl Into<List<Ty>>,
        args: &flux_rustc_bridge::ty::GenericArgs,
    ) -> Ty {
        BaseTy::Closure(did, tys.into(), args.clone()).to_ty()
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

    /// Whether the type is a `char`
    pub fn is_char(&self) -> bool {
        self.as_bty_skipping_existentials()
            .map(BaseTy::is_char)
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
            | TyKind::Blocked(_) => bug!("TODO: to_rustc for `{self:?}`"),
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
    Alias(AliasKind, AliasTy),
    Array(Ty, Const),
    Never,
    Closure(DefId, /* upvar_tys */ List<Ty>, flux_rustc_bridge::ty::GenericArgs),
    Coroutine(DefId, /*resume_ty: */ Ty, /* upvar_tys: */ List<Ty>),
    Dynamic(List<Binder<ExistentialPredicate>>, Region),
    Param(ParamTy),
    Infer(TyVid),
}

impl BaseTy {
    pub fn opaque(alias_ty: AliasTy) -> BaseTy {
        BaseTy::Alias(AliasKind::Opaque, alias_ty)
    }

    pub fn projection(alias_ty: AliasTy) -> BaseTy {
        BaseTy::Alias(AliasKind::Projection, alias_ty)
    }

    pub fn adt(adt_def: AdtDef, args: GenericArgs) -> BaseTy {
        BaseTy::Adt(adt_def, args)
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

    pub fn is_box(&self) -> bool {
        matches!(self, BaseTy::Adt(adt_def, _) if adt_def.is_box())
    }

    pub fn is_char(&self) -> bool {
        matches!(self, BaseTy::Char)
    }

    pub fn is_str(&self) -> bool {
        matches!(self, BaseTy::Str)
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
            BaseTy::Slice(_) => slice_invariants(overflow_checking),
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

    pub fn to_subset_ty_ctor(&self) -> SubsetTyCtor {
        let sort = self.sort();
        Binder::bind_with_sort(SubsetTy::trivial(self.clone(), Expr::nu()), sort)
    }

    #[track_caller]
    pub fn expect_adt(&self) -> (&AdtDef, &[GenericArg]) {
        if let BaseTy::Adt(adt_def, args) = self {
            (adt_def, args)
        } else {
            tracked_span_bug!("expected adt `{self:?}`")
        }
    }

    /// A type is an *atom* if it is "self-delimiting", i.e., it has a clear boundary
    /// when printed. This is used to avoid unnecessary parenthesis when pretty printing.
    pub fn is_atom(&self) -> bool {
        // (nilehmann) I'm not sure about this list, please adjust if you get any odd behavior
        matches!(
            self,
            BaseTy::Int(_)
                | BaseTy::Uint(_)
                | BaseTy::Slice(_)
                | BaseTy::Bool
                | BaseTy::Char
                | BaseTy::Str
                | BaseTy::Adt(..)
                | BaseTy::Tuple(..)
                | BaseTy::Param(_)
                | BaseTy::Array(..)
                | BaseTy::Never
                | BaseTy::Closure(..)
                | BaseTy::Coroutine(..)
                // opaque alias are atoms the way we print them now, but they won't
                // be if we print them as `impl Trait`
                | BaseTy::Alias(..)
        )
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
            BaseTy::Alias(kind, alias_ty) => {
                ty::Ty::new_alias(tcx, kind.to_rustc(tcx), alias_ty.to_rustc(tcx))
            }
            BaseTy::Array(ty, n) => {
                let ty = ty.to_rustc(tcx);
                let n = n.to_rustc(tcx);
                ty::Ty::new_array_with_const_len(tcx, ty, n)
            }
            BaseTy::Never => tcx.types.never,
            BaseTy::Closure(did, _, args) => ty::Ty::new_closure(tcx, *did, args.to_rustc(tcx)),
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
            BaseTy::Infer(ty_vid) => ty::Ty::new_var(tcx, *ty_vid),
        }
    }
}

#[derive(
    Clone, PartialEq, Eq, Hash, Debug, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable,
)]
pub struct AliasTy {
    pub def_id: DefId,
    pub args: GenericArgs,
    /// Holds the refinement-arguments for opaque-types; empty for projections
    pub refine_args: RefineArgs,
}

impl AliasTy {
    pub fn new(def_id: DefId, args: GenericArgs, refine_args: RefineArgs) -> Self {
        AliasTy { args, refine_args, def_id }
    }
}

/// This methods work only with associated type projections (i.e., no opaque types)
impl AliasTy {
    pub fn self_ty(&self) -> SubsetTyCtor {
        self.args[0].expect_base().clone()
    }

    pub fn with_self_ty(&self, self_ty: SubsetTyCtor) -> Self {
        Self {
            def_id: self.def_id,
            args: [GenericArg::Base(self_ty)]
                .into_iter()
                .chain(self.args.iter().skip(1).cloned())
                .collect(),
            refine_args: self.refine_args.clone(),
        }
    }
}

impl<'tcx> ToRustc<'tcx> for AliasTy {
    type T = rustc_middle::ty::AliasTy<'tcx>;

    fn to_rustc(&self, tcx: TyCtxt<'tcx>) -> Self::T {
        rustc_middle::ty::AliasTy::new(tcx, self.def_id, self.args.to_rustc(tcx))
    }
}

pub type RefineArgs = List<Expr>;

#[extension(pub trait RefineArgsExt)]
impl RefineArgs {
    fn identity_for_item(genv: GlobalEnv, def_id: DefId) -> QueryResult<RefineArgs> {
        Self::for_item(genv, def_id, |param, index| {
            Expr::var(Var::EarlyParam(EarlyReftParam { index: index as u32, name: param.name() }))
        })
    }

    fn for_item<F>(genv: GlobalEnv, def_id: DefId, mut mk: F) -> QueryResult<RefineArgs>
    where
        F: FnMut(EarlyBinder<RefineParam>, usize) -> Expr,
    {
        let reft_generics = genv.refinement_generics_of(def_id)?;
        let count = reft_generics.count();
        let mut args = Vec::with_capacity(count);
        reft_generics.fill_item(genv, &mut args, &mut mk)?;
        Ok(List::from_vec(args))
    }
}

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
            self.replace_bound_reft(&Expr::unit_struct(def_id)).to_ty()
        } else {
            Ty::exists(self.as_ref().map(SubsetTy::to_ty))
        }
    }

    pub fn to_ty_ctor(&self) -> TyCtor {
        self.as_ref().map(SubsetTy::to_ty)
    }
}

/// A subset type is a simplified version of a type that has the form `{b[e] | p}` where `b` is a
/// [`BaseTy`], `e` a refinement index, and `p` a predicate.
///
/// These are mainly found under a [`Binder`] with a single variable of the base type's sort. This
/// can be interpreted as a type constructor or an existial type. For example, under a binder with a
/// variable `v` of sort `int`, we can interpret `{i32[v] | v > 0}` as:
/// - A lambda `λv:int. {i32[v] | v > 0}` that "constructs" types when applied to ints, or
/// - An existential type `∃v:int. {i32[v] | v > 0}`.
///
/// This second interpretation is the reason we call this a subset type, i.e., the type `∃v. {b[v] | p}`
/// corresponds to the subset of values of  type `b` whose index satisfies `p`. These are the types
/// written as `B{v: p}` in the surface syntax and correspond to the types supported in other
/// refinement type systems like Liquid Haskell (with the difference that we are explicit
/// about separating refinements from program values via an index).
///
/// The main purpose for subset types is to be used as generic arguments of [kind base] when
/// interpreted as type constructors. They have two key properties that makes them suitable
/// for this:
///
/// 1. **Syntacitc Restriction**: Subset types are syntactically restricted, making it easier to
///    relate them structurally (e.g., for subtyping). For instance, given two types `S<λv. T1>` and
///    `S<λ. T2>`, if `T1` and `T2` are subset types, we know they match structurally (at least
///    shallowly). In particularly, the syntactic restriction rules out complex types like
///    `S<λv. (i32[v], i32[v])>` simplifying some operations.
///
/// 2. **Eager Canonicalization**: Subset types can be eagerly canonicalized via [*strengthening*]
///    during substitution. For example, suppose we have a function:
///    ```text
///    fn foo<T>(x: T[@a], y: { T[@b] | b == a }) { }
///    ```
///    If we instantiate `T` with `λv. { i32[v] | v > 0}`, after substitution and applying the
///    lambda (the indexing syntax `T[a]` corresponds to an application of the lambda), we get:
///    ```text
///    fn foo(x: {i32[@a] | a > 0}, y: { { i32[@b] | b > 0 } | b == a }) { }
///    ```
///    Via *strengthening* we can canonicalize this to
///    ```text
///    fn foo(x: {i32[@a] | a > 0}, y: { i32[@b] | b == a && b > 0 }) { }
///    ```
///    As a result, we can guarantee the syntactic restriction through substitution.
///
/// [kind base]: GenericParamDefKind::Base
/// [*strengthening*]: https://arxiv.org/pdf/2010.07763.pdf
#[derive(PartialEq, Clone, Eq, Hash, TyEncodable, TyDecodable)]
pub struct SubsetTy {
    /// The base type `b` in the subset type `{b[e] | p}`.
    ///
    /// **NOTE:** This is mostly going to be under a [`Binder`]. It is not yet clear to me whether
    /// this [`BaseTy`] should be able to mention variables in the binder. In general, in a type
    /// `∃v. {b[e] | p}`, it's fine to mention `v` inside `b`, but since [`SubsetTy`] is meant to
    /// facilitate syntactic manipulation we may want to restrict this.
    pub bty: BaseTy,
    /// The refinement index `e` in the subset type `{b[e] | p}`. This can be an arbitrary expression,
    /// which makes manipulation easier. However, since this is mostly found under a binder, we expect
    /// it to be [`Expr::nu()`].
    pub idx: Expr,
    /// The predicate `p` in the subset type `{b[e] | p}`.
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
        let pred = Expr::and(this.pred, pred).simplify();
        Self { bty: this.bty, idx: this.idx, pred }
    }

    pub fn to_ty(&self) -> Ty {
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
    #[track_caller]
    pub fn expect_type(&self) -> &Ty {
        if let GenericArg::Ty(ty) = self {
            ty
        } else {
            bug!("expected `rty::GenericArg::Ty`, found `{self:?}`")
        }
    }

    #[track_caller]
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
            GenericParamDefKind::Base { .. } => {
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

    pub fn identity_for_item(genv: GlobalEnv, def_id: DefId) -> QueryResult<GenericArgs> {
        Self::for_item(genv, def_id, |param, _| GenericArg::from_param_def(param))
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
            tracked_span_assert_eq!(param.index as usize, args.len()); // "{args:#?}, {generics:#?}");
            args.push(kind);
        }
        Ok(())
    }
}

impl From<TyOrBase> for GenericArg {
    fn from(v: TyOrBase) -> Self {
        match v {
            TyOrBase::Ty(ty) => GenericArg::Ty(ty),
            TyOrBase::Base(ctor) => GenericArg::Base(ctor),
        }
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

    fn rebase_onto(
        &self,
        tcx: &TyCtxt,
        source_ancestor: DefId,
        target_args: &GenericArgs,
    ) -> List<GenericArg> {
        let defs = tcx.generics_of(source_ancestor);
        target_args
            .iter()
            .chain(self.iter().skip(defs.count()))
            .cloned()
            .collect()
    }
}

#[derive(Debug)]
pub enum TyOrBase {
    Ty(Ty),
    Base(SubsetTyCtor),
}

impl TyOrBase {
    pub fn into_ty(self) -> Ty {
        match self {
            TyOrBase::Ty(ty) => ty,
            TyOrBase::Base(ctor) => ctor.to_ty(),
        }
    }

    #[track_caller]
    pub fn expect_base(self) -> SubsetTyCtor {
        match self {
            TyOrBase::Base(ctor) => ctor,
            TyOrBase::Ty(_) => tracked_span_bug!("expected `TyOrBase::Base`"),
        }
    }

    pub fn as_base(self) -> Option<SubsetTyCtor> {
        match self {
            TyOrBase::Base(ctor) => Some(ctor),
            TyOrBase::Ty(_) => None,
        }
    }
}

#[derive(Debug, Clone, TyEncodable, TyDecodable, TypeVisitable, TypeFoldable)]
pub enum TyOrCtor {
    Ty(Ty),
    Ctor(TyCtor),
}

impl TyOrCtor {
    #[track_caller]
    pub fn expect_ctor(self) -> TyCtor {
        match self {
            TyOrCtor::Ctor(ctor) => ctor,
            TyOrCtor::Ty(_) => tracked_span_bug!("expected `TyOrCtor::Ctor`"),
        }
    }

    pub fn expect_subset_ty_ctor(self) -> SubsetTyCtor {
        self.expect_ctor().map(|ty| {
            if let canonicalize::CanonicalTy::Constr(constr_ty) = ty.shallow_canonicalize()
                && let TyKind::Indexed(bty, idx) = constr_ty.ty().kind()
                && idx.is_nu()
            {
                SubsetTy::new(bty.clone(), Expr::nu(), constr_ty.pred())
            } else {
                tracked_span_bug!()
            }
        })
    }

    pub fn to_ty(&self) -> Ty {
        match self {
            TyOrCtor::Ctor(ctor) => ctor.to_ty(),
            TyOrCtor::Ty(ty) => ty.clone(),
        }
    }
}

impl From<TyOrBase> for TyOrCtor {
    fn from(v: TyOrBase) -> Self {
        match v {
            TyOrBase::Ty(ty) => TyOrCtor::Ty(ty),
            TyOrBase::Base(ctor) => TyOrCtor::Ctor(ctor.to_ty_ctor()),
        }
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
        self.parent_count + self.own_params.len()
    }

    pub fn own_count(&self) -> usize {
        self.own_params.len()
    }

    // /// Iterate and collect all parameters in this item including parents
    // pub fn collect_all_params<T, S>(
    //     &self,
    //     genv: GlobalEnv,
    //     mut f: impl FnMut(RefineParam) -> T,
    // ) -> QueryResult<S>
    // where
    //     S: FromIterator<T>,
    // {
    //     (0..self.count())
    //         .map(|i| Ok(f(self.param_at(i, genv)?)))
    //         .try_collect()
    // }
}

impl EarlyBinder<RefinementGenerics> {
    pub fn parent(&self) -> Option<DefId> {
        self.skip_binder_ref().parent
    }

    pub fn parent_count(&self) -> usize {
        self.skip_binder_ref().parent_count
    }

    pub fn count(&self) -> usize {
        self.skip_binder_ref().count()
    }

    pub fn own_count(&self) -> usize {
        self.skip_binder_ref().own_count()
    }

    pub fn own_param_at(&self, index: usize) -> EarlyBinder<RefineParam> {
        self.as_ref().map(|this| this.own_params[index].clone())
    }

    pub fn param_at(
        &self,
        param_index: usize,
        genv: GlobalEnv,
    ) -> QueryResult<EarlyBinder<RefineParam>> {
        if let Some(index) = param_index.checked_sub(self.parent_count()) {
            Ok(self.own_param_at(index))
        } else {
            let parent = self.parent().expect("parent_count > 0 but no parent?");
            genv.refinement_generics_of(parent)?
                .param_at(param_index, genv)
        }
    }

    pub fn iter_own_params(&self) -> impl Iterator<Item = EarlyBinder<RefineParam>> + use<'_> {
        self.skip_binder_ref()
            .own_params
            .iter()
            .cloned()
            .map(EarlyBinder)
    }

    pub fn fill_item<F, R>(&self, genv: GlobalEnv, vec: &mut Vec<R>, mk: &mut F) -> QueryResult
    where
        F: FnMut(EarlyBinder<RefineParam>, usize) -> R,
    {
        if let Some(def_id) = self.parent() {
            genv.refinement_generics_of(def_id)?
                .fill_item(genv, vec, mk)?;
        }
        for param in self.iter_own_params() {
            vec.push(mk(param, vec.len()));
        }
        Ok(())
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
        let idx = self.idx.clone();
        Ty::indexed(bty, idx)
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

    pub fn output(&self) -> Binder<FnOutput> {
        self.output.clone()
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
        self.sort_def().to_sort(args)
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

    pub fn is_union(&self) -> bool {
        self.0.rustc.is_union()
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

    // pub fn is_reflected(&self) -> bool {
    //     self.0.sort_def.is_reflected()
    // }
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
    // The field_idx is `Some(i)` when we have the `i`-th field of a `union`, in which case,
    // the `inputs` are _just_ the `i`-th type (and not all the types...)
    pub fn to_poly_fn_sig(&self, field_idx: Option<crate::FieldIdx>) -> EarlyBinder<PolyFnSig> {
        self.as_ref().map(|poly_variant| {
            poly_variant.as_ref().map(|variant| {
                let ret = variant.ret().shift_in_escaping(1);
                let output = Binder::bind_with_vars(FnOutput::new(ret, vec![]), List::empty());
                let inputs = match field_idx {
                    None => variant.fields.clone(),
                    Some(i) => List::singleton(variant.fields[i.index()].clone()),
                };
                let requires = List::empty();
                FnSig::new(Safety::Safe, abi::Abi::Rust, requires, inputs, output)
            })
        })
    }
}

impl TyKind {
    fn intern(self) -> Ty {
        Ty(Interned::new(self))
    }
}

/// returns the same invariants as for `usize` which is the length of a slice
fn slice_invariants(overflow_checking: bool) -> &'static [Invariant] {
    static DEFAULT: LazyLock<[Invariant; 1]> = LazyLock::new(|| {
        [Invariant { pred: Binder::bind_with_sort(Expr::ge(Expr::nu(), Expr::zero()), Sort::Int) }]
    });
    static OVERFLOW: LazyLock<[Invariant; 2]> = LazyLock::new(|| {
        [
            Invariant {
                pred: Binder::bind_with_sort(Expr::ge(Expr::nu(), Expr::zero()), Sort::Int),
            },
            Invariant {
                pred: Binder::bind_with_sort(
                    Expr::le(Expr::nu(), Expr::uint_max(UintTy::Usize)),
                    Sort::Int,
                ),
            },
        ]
    });
    if overflow_checking {
        &*OVERFLOW
    } else {
        &*DEFAULT
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
    AssocReftId,
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
    bin_rel_sorts: ItemLocalMap<Sort>,
    coercions: ItemLocalMap<Vec<Coercion>>,
    field_projs: ItemLocalMap<FieldProj>,
    node_sorts: ItemLocalMap<Sort>,
    record_ctors: ItemLocalMap<DefId>,
}

#[derive(Clone, Copy, Debug)]
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
            bin_rel_sorts: ItemLocalMap::default(),
            coercions: ItemLocalMap::default(),
            field_projs: ItemLocalMap::default(),
            node_sorts: ItemLocalMap::default(),
            record_ctors: ItemLocalMap::default(),
        }
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

    pub fn field_projs_mut(&mut self) -> LocalTableInContextMut<FieldProj> {
        LocalTableInContextMut { owner: self.owner, data: &mut self.field_projs }
    }

    pub fn field_projs(&self) -> LocalTableInContext<FieldProj> {
        LocalTableInContext { owner: self.owner, data: &self.field_projs }
    }

    pub fn node_sorts_mut(&mut self) -> LocalTableInContextMut<Sort> {
        LocalTableInContextMut { owner: self.owner, data: &mut self.node_sorts }
    }

    pub fn node_sorts(&self) -> LocalTableInContext<Sort> {
        LocalTableInContext { owner: self.owner, data: &self.node_sorts }
    }

    pub fn record_ctors_mut(&mut self) -> LocalTableInContextMut<DefId> {
        LocalTableInContextMut { owner: self.owner, data: &mut self.record_ctors }
    }

    pub fn record_ctors(&self) -> LocalTableInContext<DefId> {
        LocalTableInContext { owner: self.owner, data: &self.record_ctors }
    }
}

impl<T> LocalTableInContextMut<'_, T> {
    pub fn insert(&mut self, fhir_id: FhirId, value: T) {
        tracked_span_assert_eq!(self.owner, fhir_id.owner);
        self.data.insert(fhir_id.local_id, value);
    }
}

impl<'a, T> LocalTableInContext<'a, T> {
    pub fn get(&self, fhir_id: FhirId) -> Option<&'a T> {
        tracked_span_assert_eq!(self.owner, fhir_id.owner);
        self.data.get(&fhir_id.local_id)
    }
}
