//! Flux High-Level Intermediate Repesentation
//!
//! The fhir corresponds to the desugared version of source level flux annotations. The main
//! difference with the surface syntax is that the list of refinement parameters is explicit
//! in fhir. For example, the following signature
//!
//! `fn(x: &strg i32[@n]) ensures x: i32[n + 1]`
//!
//! desugars to
//!
//! `for<n: int, l: loc> fn(l: i32[n]; ptr(l)) ensures l: i32[n + 1]`.
//!
//! The main analysis performed on the fhir is well-formedness, thus, the fhir keeps track of
//! spans for refinement expressions to report errors.
//!
//! The name fhir is borrowed (pun intended) from rustc's hir to refer to something a bit lower
//! than the surface syntax.

pub mod lift;
pub mod visit;

use std::{borrow::Cow, fmt};

use flux_common::{bug, span_bug};
use flux_config as config;
pub use flux_fixpoint::{BinOp, UnOp};
use itertools::Itertools;
use rustc_data_structures::{
    fx::FxIndexMap,
    unord::{UnordMap, UnordSet},
};
use rustc_hash::FxHashMap;
pub use rustc_hir::PrimTy;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    ItemId, LangItem, OwnerId,
};
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
pub use rustc_middle::mir::Mutability;
use rustc_middle::{middle::resolve_bound_vars::ResolvedArg, ty::TyCtxt};
use rustc_span::{Span, Symbol};
pub use rustc_target::abi::VariantIdx;

use crate::{global_env::GlobalEnv, pretty, rty::Constant};

#[derive(Debug, Clone, Copy)]
pub struct Generics<'fhir> {
    pub params: &'fhir [GenericParam<'fhir>],
    pub refinement_params: &'fhir [RefineParam<'fhir>],
    pub self_kind: Option<GenericParamKind<'fhir>>,
    pub predicates: &'fhir [WhereBoundPredicate<'fhir>],
}

#[derive(Debug, Clone, Copy)]
pub struct GenericParam<'fhir> {
    pub def_id: LocalDefId,
    pub kind: GenericParamKind<'fhir>,
}

#[derive(Debug, Clone, Copy)]
pub enum GenericParamKind<'fhir> {
    Type { default: Option<Ty<'fhir>> },
    SplTy,
    BaseTy,
    Lifetime,
}

#[derive(Debug, Clone, Copy)]
pub struct ConstInfo {
    pub def_id: DefId,
    pub sym: Symbol,
    pub val: Constant,
}

#[derive(Debug)]
pub struct Qualifier<'fhir> {
    pub name: Symbol,
    pub args: &'fhir [RefineParam<'fhir>],
    pub expr: Expr<'fhir>,
    pub global: bool,
}

pub struct Item<'fhir> {
    pub kind: ItemKind<'fhir>,
}

pub enum ItemKind<'fhir> {
    Enum(EnumDef<'fhir>),
    Struct(StructDef<'fhir>),
    TyAlias(TyAlias<'fhir>),
    Trait(Trait<'fhir>),
    Impl(Impl<'fhir>),
    Fn(FnSig<'fhir>),
    OpaqueTy(OpaqueTy<'fhir>),
}

pub struct TraitItem<'fhir> {
    pub kind: TraitItemKind<'fhir>,
}

pub enum TraitItemKind<'fhir> {
    Fn(FnSig<'fhir>),
    Type(AssocType<'fhir>),
}

pub struct ImplItem<'fhir> {
    pub kind: ImplItemKind<'fhir>,
}

pub enum ImplItemKind<'fhir> {
    Fn(FnSig<'fhir>),
}

#[derive(Debug)]
pub enum FluxItem<'fhir> {
    Qualifier(Qualifier<'fhir>),
    Defn(Defn<'fhir>),
}

#[derive(Debug, Clone, Copy)]
pub struct SortDecl {
    pub name: Symbol,
    pub span: Span,
}

pub type SortDecls = FxHashMap<Symbol, SortDecl>;

#[derive(Debug)]
pub struct GenericPredicates<'fhir> {
    pub predicates: &'fhir [WhereBoundPredicate<'fhir>],
}

#[derive(Debug, Clone, Copy)]
pub struct WhereBoundPredicate<'fhir> {
    pub span: Span,
    pub bounded_ty: Ty<'fhir>,
    pub bounds: GenericBounds<'fhir>,
}

pub type GenericBounds<'fhir> = &'fhir [GenericBound<'fhir>];

#[derive(Debug, Clone, Copy)]
pub enum GenericBound<'fhir> {
    Trait(PolyTraitRef<'fhir>, TraitBoundModifier),
    LangItemTrait(LangItem, &'fhir [GenericArg<'fhir>], &'fhir [TypeBinding<'fhir>]),
}

#[derive(Debug, Clone, Copy)]
pub struct PolyTraitRef<'fhir> {
    pub bound_generic_params: &'fhir [GenericParam<'fhir>],
    pub trait_ref: Path<'fhir>,
}

#[derive(Debug, Copy, Clone)]
pub enum TraitBoundModifier {
    None,
    Maybe,
}

pub struct Trait<'fhir> {
    pub generics: Generics<'fhir>,
    pub assoc_predicates: &'fhir [TraitAssocPredicate<'fhir>],
}

impl<'fhir> Trait<'fhir> {
    pub fn find_assoc_predicate(&self, name: Symbol) -> Option<&'fhir TraitAssocPredicate<'fhir>> {
        self.assoc_predicates
            .iter()
            .find(|assoc_pred| assoc_pred.name == name)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TraitAssocPredicate<'fhir> {
    pub name: Symbol,
    pub sort: FuncSort<'fhir>,
    pub span: Span,
}

pub struct Impl<'fhir> {
    pub generics: Generics<'fhir>,
    pub assoc_predicates: &'fhir [ImplAssocPredicate<'fhir>],
}

impl<'fhir> Impl<'fhir> {
    pub fn find_assoc_predicate(&self, name: Symbol) -> Option<&'fhir ImplAssocPredicate<'fhir>> {
        self.assoc_predicates
            .iter()
            .find(|assoc_pred| assoc_pred.name == name)
    }
}

#[derive(Clone, Copy)]
pub struct ImplAssocPredicate<'fhir> {
    pub name: Symbol,
    pub params: &'fhir [RefineParam<'fhir>],
    pub body: Expr<'fhir>,
    pub span: Span,
}

pub struct AssocType<'fhir> {
    pub generics: Generics<'fhir>,
}

#[derive(Debug)]
pub struct OpaqueTy<'fhir> {
    pub generics: Generics<'fhir>,
    pub bounds: GenericBounds<'fhir>,
}

pub type Arena = bumpalo::Bump;

#[derive(PartialEq, Eq, Hash, Copy, Clone)]
pub enum IgnoreKey {
    /// Ignore the entire crate
    Crate,
    /// (Transitively) ignore the module named `LocalDefId`
    Module(LocalDefId),
}

/// A map between rust definitions and flux annotations in their desugared `fhir` form.
///
/// note: `Map` is a very generic name, so we typically use the type qualified as `fhir::Map`.
#[derive(Default)]
pub struct Crate<'fhir> {
    pub items: UnordMap<LocalDefId, Item<'fhir>>,
    pub trait_items: UnordMap<LocalDefId, TraitItem<'fhir>>,
    pub impl_items: UnordMap<LocalDefId, ImplItem<'fhir>>,
    pub consts: FxHashMap<Symbol, ConstInfo>,
    pub externs: UnordMap<DefId, LocalDefId>,
    pub flux_items: FxHashMap<Symbol, FluxItem<'fhir>>,
    pub fn_quals: FxHashMap<LocalDefId, &'fhir [SurfaceIdent]>,
    pub func_decls: FxHashMap<Symbol, FuncDecl<'fhir>>,
    pub trusted: UnordSet<LocalDefId>,
    pub ignores: UnordSet<IgnoreKey>,
    pub crate_config: config::CrateConfig,
}

impl<'fhir> Crate<'fhir> {
    pub fn new(ignores: UnordSet<IgnoreKey>, crate_config: Option<config::CrateConfig>) -> Self {
        Self {
            items: Default::default(),
            trait_items: Default::default(),
            impl_items: Default::default(),
            consts: Default::default(),
            externs: Default::default(),
            flux_items: Default::default(),
            fn_quals: Default::default(),
            func_decls: Default::default(),
            trusted: Default::default(),
            ignores,
            crate_config: crate_config.unwrap_or_default(),
        }
    }
}

#[derive(Debug)]
pub struct TyAlias<'fhir> {
    pub owner_id: OwnerId,
    pub generics: Generics<'fhir>,
    pub refined_by: &'fhir RefinedBy<'fhir>,
    pub ty: Ty<'fhir>,
    pub span: Span,
    pub index_params: &'fhir [RefineParam<'fhir>],
    /// Whether this alias was [lifted] from a `hir` alias
    ///
    /// [lifted]: lift::lift_type_alias
    pub lifted: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct StructDef<'fhir> {
    pub owner_id: OwnerId,
    pub generics: Generics<'fhir>,
    pub refined_by: &'fhir RefinedBy<'fhir>,
    pub params: &'fhir [RefineParam<'fhir>],
    pub kind: StructKind<'fhir>,
    pub invariants: &'fhir [Expr<'fhir>],
    /// Whether this is a spec for an extern struct
    pub extern_id: Option<DefId>,
}

#[derive(Debug, Clone, Copy)]
pub enum StructKind<'fhir> {
    Transparent { fields: &'fhir [FieldDef<'fhir>] },
    Opaque,
}

#[derive(Debug, Clone, Copy)]
pub struct FieldDef<'fhir> {
    pub def_id: LocalDefId,
    pub ty: Ty<'fhir>,
    /// Whether this field was [lifted] from a `hir` field
    ///
    /// [lifted]: lift::LiftCtxt::lift_field_def
    pub lifted: bool,
}

#[derive(Debug)]
pub struct EnumDef<'fhir> {
    pub owner_id: OwnerId,
    pub generics: Generics<'fhir>,
    pub refined_by: &'fhir RefinedBy<'fhir>,
    pub params: &'fhir [RefineParam<'fhir>],
    pub variants: &'fhir [VariantDef<'fhir>],
    pub invariants: &'fhir [Expr<'fhir>],
    /// Whether this is a expecr for an extern enum
    pub extern_id: Option<DefId>,
}

#[derive(Debug, Clone, Copy)]
pub struct VariantDef<'fhir> {
    pub def_id: LocalDefId,
    pub params: &'fhir [RefineParam<'fhir>],
    pub fields: &'fhir [FieldDef<'fhir>],
    pub ret: VariantRet<'fhir>,
    pub span: Span,
    /// Whether this variant was [lifted] from a hir variant
    ///
    /// [lifted]: lift::LiftCtxt::lift_enum_variant
    pub lifted: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct VariantRet<'fhir> {
    pub bty: BaseTy<'fhir>,
    pub idx: RefineArg<'fhir>,
}

#[derive(Clone, Copy)]
pub struct FnSig<'fhir> {
    pub generics: Generics<'fhir>,
    /// example: vec![(0 <= n), (l: i32)]
    pub requires: &'fhir [Constraint<'fhir>],
    /// example: vec![(x: StrRef(l))]
    pub args: &'fhir [Ty<'fhir>],
    pub output: FnOutput<'fhir>,
    /// Whether the sig was [lifted] from a hir signature
    ///
    /// [lifted]: lift::LiftCtxt::lift_fn_sig
    pub lifted: bool,
    pub span: Span,
}

#[derive(Clone, Copy)]
pub struct FnOutput<'fhir> {
    pub params: &'fhir [RefineParam<'fhir>],
    pub ret: Ty<'fhir>,
    pub ensures: &'fhir [Constraint<'fhir>],
}

#[derive(Clone, Copy)]
pub enum Constraint<'fhir> {
    /// A type constraint on a location
    Type(
        Ident,
        Ty<'fhir>,
        /// The index of the argument corresponding to the constraint.
        usize,
    ),
    /// A predicate that needs to hold
    Pred(Expr<'fhir>),
}

#[derive(Clone, Copy)]
pub struct Ty<'fhir> {
    pub kind: TyKind<'fhir>,
    pub span: Span,
}

#[derive(Clone, Copy)]
pub enum TyKind<'fhir> {
    /// A type that parses as a [`BaseTy`] but was written without refinements. Most types in
    /// this category are base types and will be converted into an [existential], e.g., `i32` is
    /// converted into `∃v:int. i32[v]`. However, this category also contains generic variables
    /// of kind [type] or [*special*]. We cannot distinguish these syntactially so we resolve them
    /// later in the analysis.
    ///
    /// [existential]: crate::rty::TyKind::Exists
    /// [type]: GenericParamKind::Type
    /// [*special*]: GenericParamKind::SplTy
    BaseTy(BaseTy<'fhir>),
    Indexed(BaseTy<'fhir>, RefineArg<'fhir>),
    Exists(&'fhir [RefineParam<'fhir>], &'fhir Ty<'fhir>),
    /// Constrained types `{T | p}` are like existentials but without binders, and are useful
    /// for specifying constraints on indexed values e.g. `{i32[@a] | 0 <= a}`
    Constr(Pred<'fhir>, &'fhir Ty<'fhir>),
    Ptr(Lifetime, Ident),
    Ref(Lifetime, MutTy<'fhir>),
    Tuple(&'fhir [Ty<'fhir>]),
    Array(&'fhir Ty<'fhir>, ArrayLen),
    RawPtr(&'fhir Ty<'fhir>, Mutability),
    OpaqueDef(ItemId, &'fhir [GenericArg<'fhir>], &'fhir [RefineArg<'fhir>], bool),
    Never,
    Hole(FhirId),
}

#[derive(Clone, Copy)]
pub struct MutTy<'fhir> {
    pub ty: &'fhir Ty<'fhir>,
    pub mutbl: Mutability,
}

/// Our surface syntax doesn't have lifetimes. To deal with them we create a *hole* for every lifetime
/// which we then resolve during `annot_check` when zipping against the lifted version.
#[derive(Copy, Clone)]
pub enum Lifetime {
    /// A lifetime hole created during desugaring.
    Hole(FhirId),
    /// A resolved lifetime created during lifting.
    Resolved(ResolvedArg),
}

#[derive(Clone, Copy)]
pub struct ArrayLen {
    pub val: usize,
    pub span: Span,
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum FluxLocalDefId {
    /// An item without a corresponding Rust definition, e.g., a qualifier or an uninterpreted function
    Flux(Symbol),
    /// An item with a corresponding Rust definition, e.g., struct, enum, or function.
    Rust(LocalDefId),
}

/// Owner version of [`FluxLocalDefId`]
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum FluxOwnerId {
    Flux(Symbol),
    Rust(OwnerId),
}

/// A unique identifier for a node in the AST. Like [`HirId`] it is composed of an `owner` and a
/// `local_id`. We don't generate ids for all nodes, but only for those we need to remember
/// information elaborated during well-formedness checking to later be used during conversion into
/// [`rty`].
///
/// [`rty`]: crate::rty
/// [`HirId`]: rustc_hir::HirId
#[derive(Debug, Hash, PartialEq, Eq, Copy, Clone)]
pub struct FhirId {
    pub owner: FluxOwnerId,
    pub local_id: ItemLocalId,
}

newtype_index! {
    /// An `ItemLocalId` uniquely identifies something within a given "item-like".
    pub struct ItemLocalId {}
}

#[derive(Clone, Copy)]
pub struct RefineArg<'fhir> {
    pub kind: RefineArgKind<'fhir>,
    pub fhir_id: FhirId,
    pub span: Span,
}

impl<'fhir> RefineArg<'fhir> {
    pub fn is_colon_param(&self) -> Option<Ident> {
        if let RefineArgKind::Expr(expr) = &self.kind
            && let ExprKind::Var(var, Some(ParamKind::Colon)) = &expr.kind
        {
            Some(*var)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
pub enum RefineArgKind<'fhir> {
    Expr(Expr<'fhir>),
    Abs(&'fhir [RefineParam<'fhir>], Expr<'fhir>),
    Record(&'fhir [RefineArg<'fhir>]),
}

/// These are types of things that may be refined with indices or existentials
#[derive(Clone, Copy)]
pub struct BaseTy<'fhir> {
    pub kind: BaseTyKind<'fhir>,
    pub span: Span,
}

#[derive(Clone, Copy)]
pub enum BaseTyKind<'fhir> {
    Path(QPath<'fhir>),
    Slice(&'fhir Ty<'fhir>),
}

#[derive(Clone, Copy)]
pub enum QPath<'fhir> {
    Resolved(Option<&'fhir Ty<'fhir>>, Path<'fhir>),
}

#[derive(Clone, Copy)]
pub struct Path<'fhir> {
    pub res: Res,
    pub args: &'fhir [GenericArg<'fhir>],
    pub bindings: &'fhir [TypeBinding<'fhir>],
    pub refine: &'fhir [RefineArg<'fhir>],
    pub span: Span,
}

#[derive(Clone, Copy)]
pub struct TypeBinding<'fhir> {
    pub ident: SurfaceIdent,
    pub term: Ty<'fhir>,
}

#[derive(Clone, Copy)]
pub enum GenericArg<'fhir> {
    Lifetime(Lifetime),
    Type(&'fhir Ty<'fhir>),
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum Res {
    Def(DefKind, DefId),
    PrimTy(PrimTy),
    SelfTyAlias { alias_to: DefId, is_trait_impl: bool },
    SelfTyParam { trait_: DefId },
}

#[derive(Debug, Clone, Copy)]
pub struct RefineParam<'fhir> {
    pub ident: Ident,
    pub sort: Sort<'fhir>,
    pub kind: ParamKind,
    pub fhir_id: FhirId,
    pub span: Span,
}

impl<'fhir> RefineParam<'fhir> {
    pub fn name(&self) -> Name {
        self.ident.name
    }
}

/// How the parameter was declared in the surface syntax. This is used to adjust how errors are
/// reported and to control the [inference mode].
///
/// [inference mode]: InferMode
#[derive(Debug, Clone, Copy)]
pub enum ParamKind {
    /// A parameter declared in an explicit scope, e.g., `fn foo<refine n: int>(x: i32[n])`
    Explicit,
    /// An implicitly scoped parameter declared with `@a` syntax
    At,
    /// An implicitly scoped parameter declared with `#a` syntax
    Pound,
    /// An implicitly scoped parameter declared with `x: T` syntax
    Colon,
    /// A location declared with `x: &strg T` syntax
    Loc(usize),
}

impl ParamKind {
    pub(crate) fn is_implicit(&self) -> bool {
        matches!(self, ParamKind::At | ParamKind::Pound | ParamKind::Colon)
    }
}

/// *Infer*ence *mode* for a parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum InferMode {
    /// Generate a fresh evar for the parameter and solve it via syntactic unification. The parameter
    /// must appear at least once as an index for unification to succeed, but otherwise it can appear
    /// (mostly) freely.
    EVar,
    /// Generate a fresh kvar and let fixpoint infer it. This mode can only be used with abstract
    /// refinement predicates. If the parameter is marked as kvar then it can only appear in
    /// positions that will result in a _horn_ constraint as required by fixpoint.
    KVar,
}

#[derive(Clone, Copy)]
pub enum SortCtor {
    Set,
    Map,
    /// User defined opaque sort
    User {
        name: Symbol,
    },
}

#[derive(Clone, Copy)]
pub enum Sort<'fhir> {
    Int,
    Bool,
    Real,
    Loc,
    BitVec(usize),
    /// Sort constructor application (e.g. `Set<int>` or `Map<int, int>`)
    App(SortCtor, &'fhir [Sort<'fhir>]),
    Func(PolyFuncSort<'fhir>),
    /// sort variable
    Var(usize),
    /// A record sort corresponds to the sort associated with a type alias or an adt (struct/enum).
    /// Values of a record sort can be projected using dot notation to extract their fields.
    /// the `List<Sort>` is for the type parameters of (generic) record sorts
    Record(DefId, &'fhir [Sort<'fhir>]),
    /// The sort associated to a type variable
    Param(DefId),
    /// The sort of the `Self` type, as used within a trait.
    SelfParam {
        /// The trait this `Self` is a generic parameter for.
        trait_id: DefId,
    },
    /// The sort of a `Self` type, as used somewhere other than within a trait.
    SelfAlias {
        /// The item introducing the `Self` type alias, e.g., an impl block
        alias_to: DefId,
    },
    /// A sort that needs to be inferred
    Infer,
}

#[derive(Clone, Copy)]
pub struct FuncSort<'fhir> {
    /// inputs and output in order
    pub inputs_and_output: &'fhir [Sort<'fhir>],
}

#[derive(Clone, Copy)]
pub struct PolyFuncSort<'fhir> {
    pub params: usize,
    pub fsort: FuncSort<'fhir>,
}

impl<'fhir> PolyFuncSort<'fhir> {
    pub fn new(params: usize, inputs_and_output: &'fhir [Sort]) -> Self {
        let fsort = FuncSort { inputs_and_output };
        Self { params, fsort }
    }
}

#[derive(Clone, Copy)]
pub struct Pred<'fhir> {
    pub kind: PredKind<'fhir>,
    pub span: Span,
    pub fhir_id: FhirId,
}

#[derive(Clone, Copy)]
pub enum PredKind<'fhir> {
    Expr(Expr<'fhir>),
    Alias(AliasPred<'fhir>, &'fhir [RefineArg<'fhir>]),
}

#[derive(Clone, Copy)]
pub struct AliasPred<'fhir> {
    pub trait_id: DefId,
    pub name: Symbol,
    pub generic_args: &'fhir [GenericArg<'fhir>],
}

#[derive(Clone, Copy)]
pub struct Expr<'fhir> {
    pub kind: ExprKind<'fhir>,
    pub span: Span,
    pub fhir_id: FhirId,
}

#[derive(Clone, Copy)]
pub enum ExprKind<'fhir> {
    Const(DefId, Span),
    Var(Ident, Option<ParamKind>),
    Dot(Ident, SurfaceIdent),
    Literal(Lit),
    BinaryOp(BinOp, &'fhir Expr<'fhir>, &'fhir Expr<'fhir>),
    UnaryOp(UnOp, &'fhir Expr<'fhir>),
    App(Func, &'fhir [Expr<'fhir>]),
    IfThenElse(&'fhir Expr<'fhir>, &'fhir Expr<'fhir>, &'fhir Expr<'fhir>),
}

#[derive(Clone, Copy)]
pub enum Func {
    /// A function coming from a refinement parameter.
    Var(Ident, FhirId),
    /// A _global_ function symbol (including possibly theory symbols).
    Global(Symbol, FuncKind, Span, FhirId),
}

#[derive(Clone, Copy)]
pub enum Lit {
    Int(i128),
    Real(i128),
    Bool(bool),
}

pub type SurfaceIdent = rustc_span::symbol::Ident;

#[derive(Clone, Copy)]
pub struct Ident {
    pub name: Name,
    pub source_info: SurfaceIdent,
}

newtype_index! {
    #[debug_format = "a{}"]
    pub struct Name {}
}

impl<'fhir> PolyTraitRef<'fhir> {
    pub fn trait_def_id(&self) -> DefId {
        let path = &self.trait_ref;
        if let Res::Def(DefKind::Trait, did) = path.res {
            did
        } else {
            span_bug!(path.span, "unexpected resolution {:?}", path.res);
        }
    }
}

impl From<FluxOwnerId> for FluxLocalDefId {
    fn from(flux_id: FluxOwnerId) -> Self {
        match flux_id {
            FluxOwnerId::Flux(sym) => FluxLocalDefId::Flux(sym),
            FluxOwnerId::Rust(owner_id) => FluxLocalDefId::Rust(owner_id.def_id),
        }
    }
}

impl From<LocalDefId> for FluxLocalDefId {
    fn from(def_id: LocalDefId) -> Self {
        FluxLocalDefId::Rust(def_id)
    }
}

impl From<OwnerId> for FluxOwnerId {
    fn from(owner_id: OwnerId) -> Self {
        FluxOwnerId::Rust(owner_id)
    }
}

impl SortCtor {
    pub fn arity(&self) -> usize {
        match self {
            SortCtor::Set => 1,
            SortCtor::Map => 2,
            SortCtor::User { .. } => 0,
        }
    }
}

impl<'fhir> Ty<'fhir> {
    pub fn as_path(&self) -> Option<Path<'fhir>> {
        match &self.kind {
            TyKind::BaseTy(bty) => bty.as_path(),
            _ => None,
        }
    }
}

impl<'fhir> BaseTy<'fhir> {
    fn as_path(&self) -> Option<Path<'fhir>> {
        match self.kind {
            BaseTyKind::Path(QPath::Resolved(None, path)) => Some(path),
            _ => None,
        }
    }
}

impl Res {
    pub fn descr(&self) -> &'static str {
        match self {
            Res::PrimTy(_) => "builtin type",
            Res::Def(kind, def_id) => kind.descr(*def_id),
            Res::SelfTyAlias { .. } | Res::SelfTyParam { .. } => "self type",
        }
    }

    pub fn is_box(&self, tcx: TyCtxt) -> bool {
        if let Res::Def(DefKind::Struct, def_id) = self {
            tcx.adt_def(def_id).is_box()
        } else {
            false
        }
    }
}

impl<Id> TryFrom<rustc_hir::def::Res<Id>> for Res {
    type Error = ();

    fn try_from(res: rustc_hir::def::Res<Id>) -> Result<Self, Self::Error> {
        match res {
            rustc_hir::def::Res::Def(kind, did) => Ok(Res::Def(kind, did)),
            rustc_hir::def::Res::PrimTy(prim_ty) => Ok(Res::PrimTy(prim_ty)),
            rustc_hir::def::Res::SelfTyAlias { alias_to, forbid_generic: false, is_trait_impl } => {
                Ok(Res::SelfTyAlias { alias_to, is_trait_impl })
            }
            rustc_hir::def::Res::SelfTyParam { trait_ } => Ok(Res::SelfTyParam { trait_ }),
            _ => Err(()),
        }
    }
}

impl<'fhir> QPath<'fhir> {
    pub fn span(&self) -> Span {
        match self {
            QPath::Resolved(_, path) => path.span,
        }
    }
}

impl<'fhir> From<QPath<'fhir>> for BaseTy<'fhir> {
    fn from(qpath: QPath<'fhir>) -> Self {
        let span = qpath.span();
        Self { kind: BaseTyKind::Path(qpath), span }
    }
}

impl Func {
    pub fn fhir_id(&self) -> FhirId {
        match self {
            Func::Var(_, fhir_id) => *fhir_id,
            Func::Global(_, _, _, fhir_id) => *fhir_id,
        }
    }
}

impl Lit {
    pub const TRUE: Lit = Lit::Bool(true);
}

impl Ident {
    pub fn new(name: Name, source_info: SurfaceIdent) -> Self {
        Ident { name, source_info }
    }

    pub fn span(&self) -> Span {
        self.source_info.span
    }

    pub fn sym(&self) -> Symbol {
        self.source_info.name
    }
}

/// Information about the refinement parameters associated with a type alias or a struct/enum.
#[derive(Clone, Debug)]
pub struct RefinedBy<'fhir> {
    pub def_id: LocalDefId,
    pub span: Span,
    /// Tracks the mapping from bound var to generic def ids. e.g. if we have
    ///
    /// ```ignore
    /// #[refined_by(keys: Set<K>)]
    /// RMap<K, V> { ...}
    /// ```
    /// then the sort associated to `RMap` is of the form `forall #0. { keys: Set<#0> }`
    /// and `sort_params` will be `vec![K]`,  i.e., it maps `Var(0)` to `K`.
    pub sort_params: Vec<DefId>,
    /// Index parameters indexed by their name and in the same order they appear in the definition.
    pub index_params: FxIndexMap<Symbol, Sort<'fhir>>,
}

#[derive(Debug)]
pub struct FuncDecl<'fhir> {
    pub name: Symbol,
    pub sort: PolyFuncSort<'fhir>,
    pub kind: FuncKind,
}

#[derive(Debug, Clone, Copy, TyEncodable, TyDecodable, PartialEq, Eq, Hash)]
pub enum FuncKind {
    /// Theory symbols "interpreted" by the SMT solver: `Symbol` is Fixpoint's name for the operation e.g. `set_cup` for flux's `set_union`
    Thy(Symbol),
    /// User-defined uninterpreted functions with no definition
    Uif,
    /// User-defined functions with a body definition
    Def,
}

#[derive(Debug)]
pub struct Defn<'fhir> {
    pub name: Symbol,
    pub params: usize,
    pub args: &'fhir [RefineParam<'fhir>],
    pub sort: Sort<'fhir>,
    pub expr: Expr<'fhir>,
}

impl<'fhir> Generics<'fhir> {
    pub(crate) fn get_param(&self, def_id: LocalDefId) -> &'fhir GenericParam<'fhir> {
        self.params.iter().find(|p| p.def_id == def_id).unwrap()
    }

    pub fn with_refined_by(self, genv: GlobalEnv<'fhir, '_>, refined_by: &RefinedBy) -> Self {
        let params = genv.alloc_slice_fill_iter(self.params.iter().map(|param| {
            let kind = if refined_by.is_base_generic(param.def_id.to_def_id()) {
                GenericParamKind::SplTy
            } else {
                param.kind
            };
            GenericParam { def_id: param.def_id, kind }
        }));
        Generics { params, ..self }
    }
}

impl<'fhir> RefinedBy<'fhir> {
    pub fn new(
        def_id: LocalDefId,
        index_params: impl IntoIterator<Item = (Symbol, Sort<'fhir>)>,
        sort_params: Vec<DefId>,
        span: Span,
    ) -> Self {
        let index_params: FxIndexMap<_, _> = index_params.into_iter().collect();
        RefinedBy { def_id, span, sort_params, index_params }
    }

    pub fn trivial(def_id: LocalDefId, span: Span) -> Self {
        RefinedBy {
            def_id,
            sort_params: Default::default(),
            span,
            index_params: Default::default(),
        }
    }

    fn is_base_generic(&self, def_id: DefId) -> bool {
        self.sort_params.contains(&def_id)
    }
}

impl<'fhir> From<PolyFuncSort<'fhir>> for Sort<'fhir> {
    fn from(fsort: PolyFuncSort<'fhir>) -> Self {
        Self::Func(fsort)
    }
}

impl<'fhir> FuncSort<'fhir> {
    pub fn inputs(&self) -> &[Sort] {
        &self.inputs_and_output[..self.inputs_and_output.len() - 1]
    }

    pub fn output(&self) -> &Sort {
        &self.inputs_and_output[self.inputs_and_output.len() - 1]
    }
}

impl rustc_errors::IntoDiagnosticArg for Ty<'_> {
    fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
        rustc_errors::DiagnosticArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

impl rustc_errors::IntoDiagnosticArg for Path<'_> {
    fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
        rustc_errors::DiagnosticArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

impl<'fhir> GenericArg<'fhir> {
    pub fn expect_type(&self) -> &'fhir Ty<'fhir> {
        if let GenericArg::Type(ty) = self {
            ty
        } else {
            bug!("expected `GenericArg::Type`")
        }
    }
}

impl<'fhir> StructDef<'fhir> {
    pub fn is_opaque(&self) -> bool {
        matches!(self.kind, StructKind::Opaque)
    }
}

impl fmt::Debug for FnSig<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.generics.refinement_params.is_empty() {
            write!(
                f,
                "for<{}> ",
                self.generics
                    .refinement_params
                    .iter()
                    .format_with(", ", |param, f| {
                        f(&format_args!("{:?}: {:?}", param.ident, param.sort))
                    })
            )?;
        }
        if !self.requires.is_empty() {
            write!(f, "[{:?}] ", self.requires.iter().format(", "))?;
        }
        write!(f, "fn({:?}) -> {:?}", self.args.iter().format(", "), self.output)
    }
}

impl fmt::Debug for FnOutput<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.params.is_empty() {
            write!(
                f,
                "exists<{}> ",
                self.params.iter().format_with(", ", |param, f| {
                    f(&format_args!("{:?}: {:?}", param.ident, param.sort))
                })
            )?;
        }
        write!(f, "{:?}", self.ret)?;
        if !self.ensures.is_empty() {
            write!(f, "; [{:?}]", self.ensures.iter().format(", "))?;
        }

        Ok(())
    }
}

impl fmt::Debug for Constraint<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Type(loc, _, ty) => write!(f, "{loc:?}: {ty:?}"),
            Constraint::Pred(e) => write!(f, "{e:?}"),
        }
    }
}

impl fmt::Debug for Ty<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TyKind::BaseTy(bty) => write!(f, "{bty:?}"),
            TyKind::Indexed(bty, idx) => write!(f, "{bty:?}[{idx:?}]"),
            TyKind::Exists(params, ty) => {
                write!(f, "{{")?;
                write!(
                    f,
                    "{}",
                    params.iter().format_with(",", |param, f| {
                        f(&format_args!("{:?}:{:?}", param.ident, param.sort))
                    })
                )?;
                if let TyKind::Constr(pred, ty) = &ty.kind {
                    write!(f, ". {ty:?} | {pred:?}}}")
                } else {
                    write!(f, ". {ty:?}}}")
                }
            }
            TyKind::Ptr(lft, loc) => write!(f, "ref<{lft:?}, {loc:?}>"),
            TyKind::Ref(lft, mut_ty) => {
                write!(f, "&{lft:?} {}{:?}", mut_ty.mutbl.prefix_str(), mut_ty.ty)
            }
            TyKind::Tuple(tys) => write!(f, "({:?})", tys.iter().format(", ")),
            TyKind::Array(ty, len) => write!(f, "[{ty:?}; {len:?}]"),
            TyKind::Never => write!(f, "!"),
            TyKind::Constr(pred, ty) => write!(f, "{{{ty:?} | {pred:?}}}"),
            TyKind::RawPtr(ty, Mutability::Not) => write!(f, "*const {ty:?}"),
            TyKind::RawPtr(ty, Mutability::Mut) => write!(f, "*mut {ty:?}"),
            TyKind::Hole(_) => write!(f, "_"),
            TyKind::OpaqueDef(def_id, args, refine_args, _) => {
                write!(
                    f,
                    "impl trait <def_id = {def_id:?}, args = {args:?}, refine = {refine_args:?}>"
                )
            }
        }
    }
}

impl fmt::Debug for Lifetime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lifetime::Hole(_) => write!(f, "'_"),
            Lifetime::Resolved(lft) => write!(f, "{lft:?}"),
        }
    }
}

impl fmt::Debug for ArrayLen {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_")
    }
}

impl fmt::Debug for BaseTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            BaseTyKind::Path(qpath) => write!(f, "{qpath:?}"),
            BaseTyKind::Slice(ty) => write!(f, "[{ty:?}]"),
        }
    }
}

impl fmt::Debug for QPath<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QPath::Resolved(_self_ty, path) => {
                write!(f, "{path:?}")
            }
        }
    }
}

impl fmt::Debug for Path<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.res {
            Res::PrimTy(PrimTy::Int(int_ty)) => {
                write!(f, "{}", int_ty.name_str())?;
            }
            Res::PrimTy(PrimTy::Uint(uint_ty)) => {
                write!(f, "{}", uint_ty.name_str())?;
            }
            Res::PrimTy(PrimTy::Float(float_ty)) => {
                write!(f, "{}", float_ty.name_str())?;
            }
            Res::PrimTy(PrimTy::Bool) => write!(f, "bool")?,
            Res::PrimTy(PrimTy::Str) => write!(f, "str")?,
            Res::PrimTy(PrimTy::Char) => write!(f, "char")?,
            Res::Def(_, def_id) => {
                write!(f, "{}", pretty::def_id_to_string(def_id))?;
            }
            Res::SelfTyAlias { .. } | Res::SelfTyParam { .. } => write!(f, "Self")?,
        }
        let args: Vec<_> = self
            .args
            .iter()
            .map(|a| a as &dyn std::fmt::Debug)
            .chain(self.bindings.iter().map(|b| b as &dyn std::fmt::Debug))
            .collect();
        if !args.is_empty() {
            write!(f, "<{:?}>", args.iter().format(", "))?;
        }
        if !self.refine.is_empty() {
            write!(f, "({:?})", self.refine.iter().format(", "))?;
        }
        Ok(())
    }
}

impl fmt::Debug for GenericArg<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GenericArg::Type(ty) => write!(f, "{ty:?}"),
            GenericArg::Lifetime(lft) => write!(f, "{lft:?}"),
        }
    }
}

impl fmt::Debug for TypeBinding<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} = {:?}", self.ident, self.term)
    }
}

impl fmt::Debug for RefineArg<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            RefineArgKind::Expr(expr) => {
                write!(f, "{expr:?}")
            }
            RefineArgKind::Abs(params, body) => {
                write!(
                    f,
                    "|{}| {body:?}",
                    params.iter().format_with(", ", |param, f| {
                        f(&format_args!("{:?}: {:?}", param.ident, param.sort))
                    })
                )
            }
            RefineArgKind::Record(flds) => {
                write!(f, "{{ {:?} }}", flds.iter().format(", "))
            }
        }
    }
}

impl fmt::Debug for AliasPred<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{:?} as <{:?}>::{:?}", self.generic_args[0], self.trait_id, self.name)
    }
}

impl fmt::Debug for Pred<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            PredKind::Expr(expr) => write!(f, "{expr:?}"),
            PredKind::Alias(alias_pred, refine_args) => {
                write!(f, "{alias_pred:?}({:?})", refine_args.iter().format(", "))
            }
        }
    }
}

impl fmt::Debug for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ExprKind::Var(x, ..) => write!(f, "{x:?}"),
            ExprKind::BinaryOp(op, e1, e2) => write!(f, "({e1:?} {op:?} {e2:?})"),
            ExprKind::UnaryOp(op, e) => write!(f, "{op:?}{e:?}"),
            ExprKind::Literal(lit) => write!(f, "{lit:?}"),
            ExprKind::Const(x, _) => write!(f, "{}", pretty::def_id_to_string(*x)),
            ExprKind::App(uf, es) => write!(f, "{uf:?}({:?})", es.iter().format(", ")),
            ExprKind::IfThenElse(p, e1, e2) => {
                write!(f, "(if {p:?} {{ {e1:?} }} else {{ {e2:?} }})")
            }
            ExprKind::Dot(var, fld) => write!(f, "{var:?}.{fld}"),
        }
    }
}

impl fmt::Debug for Func {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(func, _) => write!(f, "{func:?}"),
            Self::Global(sym, ..) => write!(f, "{sym}"),
        }
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.name)
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Int(i) => write!(f, "{i}"),
            Lit::Real(r) => write!(f, "{r}real"),
            Lit::Bool(b) => write!(f, "{b}"),
        }
    }
}

impl fmt::Debug for SortCtor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SortCtor::Set => write!(f, "Set"),
            SortCtor::Map => write!(f, "Map"),
            SortCtor::User { name, .. } => write!(f, "{}", name),
        }
    }
}

impl fmt::Debug for Sort<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "bool"),
            Sort::Int => write!(f, "int"),
            Sort::Real => write!(f, "real"),
            Sort::Var(n) => write!(f, "@{}", n),
            Sort::BitVec(w) => write!(f, "bitvec({w})"),
            Sort::Loc => write!(f, "loc"),
            Sort::Func(fsort) => write!(f, "{fsort:?}"),
            Sort::Record(def_id, sort_args) => {
                if sort_args.is_empty() {
                    write!(f, "{}", pretty::def_id_to_string(*def_id))
                } else {
                    write!(
                        f,
                        "{}<{:?}>",
                        pretty::def_id_to_string(*def_id),
                        sort_args.iter().format(", ")
                    )
                }
            }
            Sort::Param(def_id) => write!(f, "sortof({})", pretty::def_id_to_string(*def_id)),
            Sort::SelfParam { trait_id } => {
                write!(f, "sortof({}::Self)", pretty::def_id_to_string(*trait_id))
            }
            Sort::SelfAlias { alias_to } => {
                write!(f, "sortof({}::Self)", pretty::def_id_to_string(*alias_to))
            }
            Sort::Infer => write!(f, "_"),
            Sort::App(ctor, args) => write!(f, "{ctor:?}<{:?}>", args.iter().format(", ")),
        }
    }
}

impl fmt::Debug for PolyFuncSort<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.params > 0 {
            write!(f, "for<{}>{:?}", self.params, self.fsort)
        } else {
            write!(f, "{:?}", self.fsort)
        }
    }
}

impl fmt::Debug for FuncSort<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.inputs() {
            [input] => {
                write!(f, "{:?} -> {:?}", input, self.output())
            }
            inputs => {
                write!(f, "({:?}) -> {:?}", inputs.iter().format(", "), self.output())
            }
        }
    }
}
