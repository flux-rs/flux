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

use std::{
    borrow::{Borrow, Cow},
    fmt,
};

use flux_common::{bug, span_bug};
pub use flux_fixpoint::{BinOp, UnOp};
use itertools::Itertools;
use rustc_data_structures::{
    fx::FxIndexMap,
    unord::{ExtendUnord, UnordMap, UnordSet},
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

use crate::{pretty, rty::Constant};

#[derive(Debug)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub refinement_params: Vec<RefineParam>,
    pub self_kind: Option<GenericParamKind>,
    pub predicates: Vec<WhereBoundPredicate>,
}

#[derive(Debug)]
pub struct GenericParam {
    pub def_id: LocalDefId,
    pub kind: GenericParamKind,
}

#[derive(Debug, Clone)]
pub enum GenericParamKind {
    Type { default: Option<Ty> },
    SplTy,
    BaseTy,
    Lifetime,
}

#[derive(Debug, Clone)]
pub struct ConstInfo {
    pub def_id: DefId,
    pub sym: Symbol,
    pub val: Constant,
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: Symbol,
    pub args: Vec<RefineParam>,
    pub expr: Expr,
    pub global: bool,
}

#[derive(Debug)]
pub enum FluxItem {
    Qualifier(Qualifier),
    Defn(Defn),
}

#[derive(Debug)]
pub struct SortDecl {
    pub name: Symbol,
    pub span: Span,
}

pub type SortDecls = FxHashMap<Symbol, SortDecl>;

#[derive(Debug)]
pub struct GenericPredicates {
    pub predicates: Vec<WhereBoundPredicate>,
}

#[derive(Debug)]
pub struct WhereBoundPredicate {
    pub span: Span,
    pub bounded_ty: Ty,
    pub bounds: GenericBounds,
}

pub type GenericBounds = Vec<GenericBound>;

#[derive(Debug)]
pub enum GenericBound {
    Trait(PolyTraitRef, TraitBoundModifier),
    LangItemTrait(LangItem, Vec<GenericArg>, Vec<TypeBinding>),
}

#[derive(Debug)]
pub struct PolyTraitRef {
    pub bound_generic_params: Vec<GenericParam>,
    pub trait_ref: Path,
}

#[derive(Debug, Copy, Clone)]
pub enum TraitBoundModifier {
    None,
    Maybe,
}

pub struct Trait {
    pub generics: Generics,
    pub assoc_predicates: Vec<TraitAssocPredicate>,
}

impl Trait {
    pub fn find_assoc_predicate(&self, name: Symbol) -> Option<&TraitAssocPredicate> {
        self.assoc_predicates
            .iter()
            .find(|assoc_pred| assoc_pred.name == name)
    }
}

#[derive(Debug)]
pub struct TraitAssocPredicate {
    pub name: Symbol,
    pub sort: FuncSort,
    pub span: Span,
}

pub struct Impl {
    pub generics: Generics,
    pub assoc_predicates: Vec<ImplAssocPredicate>,
}

impl Impl {
    pub fn find_assoc_predicate(&self, name: Symbol) -> Option<&ImplAssocPredicate> {
        self.assoc_predicates
            .iter()
            .find(|assoc_pred| assoc_pred.name == name)
    }
}

pub struct ImplAssocPredicate {
    pub name: Symbol,
    pub params: Vec<RefineParam>,
    pub body: Expr,
    pub span: Span,
}

pub struct AssocType {
    pub generics: Generics,
}

#[derive(Debug)]
pub struct OpaqueTy {
    pub generics: Generics,
    pub bounds: GenericBounds,
}

/// A map between rust definitions and flux annotations in their desugared `fhir` form.
///
/// note: `Map` is a very generic name, so we typically use the type qualified as `fhir::Map`.
#[derive(Default)]
pub struct Map {
    assoc_types: UnordMap<LocalDefId, AssocType>,
    traits: UnordMap<LocalDefId, Trait>,
    impls: UnordMap<LocalDefId, Impl>,
    opaque_tys: UnordMap<LocalDefId, OpaqueTy>,
    func_decls: FxHashMap<Symbol, FuncDecl>,
    sort_decls: SortDecls,
    flux_items: FxHashMap<Symbol, FluxItem>,
    consts: FxHashMap<Symbol, ConstInfo>,
    refined_by: UnordMap<LocalDefId, RefinedBy>,
    type_aliases: FxHashMap<LocalDefId, TyAlias>,
    structs: FxHashMap<LocalDefId, StructDef>,
    enums: FxHashMap<LocalDefId, EnumDef>,
    fns: FxHashMap<LocalDefId, FnSig>,
    fn_quals: FxHashMap<LocalDefId, Vec<SurfaceIdent>>,
    trusted: UnordSet<LocalDefId>,
    externs: UnordMap<DefId, LocalDefId>,
}

#[derive(Debug)]
pub struct TyAlias {
    pub owner_id: OwnerId,
    pub generics: Generics,
    pub ty: Ty,
    pub span: Span,
    pub index_params: Vec<RefineParam>,
    /// Whether this alias was [lifted] from a `hir` alias
    ///
    /// [lifted]: lift::lift_type_alias
    pub lifted: bool,
}

#[derive(Debug)]
pub struct StructDef {
    pub owner_id: OwnerId,
    pub generics: Generics,
    pub params: Vec<RefineParam>,
    pub kind: StructKind,
    pub invariants: Vec<Expr>,
    /// Whether this is a spec for an extern struct
    pub extern_id: Option<DefId>,
}

#[derive(Debug)]
pub enum StructKind {
    Transparent { fields: Vec<FieldDef> },
    Opaque,
}

#[derive(Debug)]
pub struct FieldDef {
    pub def_id: LocalDefId,
    pub ty: Ty,
    /// Whether this field was [lifted] from a `hir` field
    ///
    /// [lifted]: lift::LiftCtxt::lift_field_def
    pub lifted: bool,
}

#[derive(Debug)]
pub struct EnumDef {
    pub owner_id: OwnerId,
    pub generics: Generics,
    pub params: Vec<RefineParam>,
    pub variants: Vec<VariantDef>,
    pub invariants: Vec<Expr>,
    /// Whether this is a expecr for an extern enum
    pub extern_id: Option<DefId>,
}

#[derive(Debug)]
pub struct VariantDef {
    pub def_id: LocalDefId,
    pub params: Vec<RefineParam>,
    pub fields: Vec<FieldDef>,
    pub ret: VariantRet,
    pub span: Span,
    /// Whether this variant was [lifted] from a hir variant
    ///
    /// [lifted]: lift::LiftCtxt::lift_enum_variant
    pub lifted: bool,
}

#[derive(Debug)]
pub struct VariantRet {
    pub bty: BaseTy,
    pub idx: RefineArg,
}

pub struct FnSig {
    pub generics: Generics,
    /// example: vec![(0 <= n), (l: i32)]
    pub requires: Vec<Constraint>,
    /// example: vec![(x: StrRef(l))]
    pub args: Vec<Ty>,
    pub output: FnOutput,
    /// Whether the sig was [lifted] from a hir signature
    ///
    /// [lifted]: lift::LiftCtxt::lift_fn_sig
    pub lifted: bool,
    pub span: Span,
}

pub struct FnOutput {
    pub params: Vec<RefineParam>,
    pub ret: Ty,
    pub ensures: Vec<Constraint>,
}

pub enum Constraint {
    /// A type constraint on a location
    Type(
        Ident,
        Ty,
        /// The index of the argument corresponding to the constraint.
        usize,
    ),
    /// A predicate that needs to hold
    Pred(Expr),
}

#[derive(Clone)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Clone)]
pub enum TyKind {
    /// A type that parses as a [`BaseTy`] but was written without refinements. Most types in
    /// this category are base types and will be converted into an [existential], e.g., `i32` is
    /// converted into `∃v:int. i32[v]`. However, this category also contains generic variables
    /// of kind [type] or [*special*]. We cannot distinguish these syntactially so we resolve them
    /// later in the analysis.
    ///
    /// [existential]: crate::rty::TyKind::Exists
    /// [type]: GenericParamKind::Type
    /// [*special*]: GenericParamKind::SplTy
    BaseTy(BaseTy),
    Indexed(BaseTy, RefineArg),
    Exists(Vec<RefineParam>, Box<Ty>),
    /// Constrained types `{T | p}` are like existentials but without binders, and are useful
    /// for specifying constraints on indexed values e.g. `{i32[@a] | 0 <= a}`
    Constr(Pred, Box<Ty>),
    Ptr(Lifetime, Ident),
    Ref(Lifetime, MutTy),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, ArrayLen),
    RawPtr(Box<Ty>, Mutability),
    OpaqueDef(ItemId, Vec<GenericArg>, Vec<RefineArg>, bool),
    Never,
    Hole(FhirId),
}

#[derive(Clone)]
pub struct MutTy {
    pub ty: Box<Ty>,
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

#[derive(Clone)]
pub struct ArrayLen {
    pub val: usize,
    pub span: Span,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum WeakKind {
    Shr,
    Mut,
    Arr,
}

impl From<Mutability> for WeakKind {
    fn from(mutbl: Mutability) -> WeakKind {
        match mutbl {
            Mutability::Not => WeakKind::Shr,
            Mutability::Mut => WeakKind::Mut,
        }
    }
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

#[derive(Clone)]
pub struct RefineArg {
    pub kind: RefineArgKind,
    pub fhir_id: FhirId,
    pub span: Span,
}

impl RefineArg {
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

#[derive(Clone)]
pub enum RefineArgKind {
    Expr(Expr),
    Abs(Vec<RefineParam>, Expr),
    Record(Vec<RefineArg>),
}

/// These are types of things that may be refined with indices or existentials
#[derive(Clone)]
pub struct BaseTy {
    pub kind: BaseTyKind,
    pub span: Span,
}

#[derive(Clone)]
pub enum BaseTyKind {
    Path(QPath),
    Slice(Box<Ty>),
}

#[derive(Clone)]
pub enum QPath {
    Resolved(Option<Box<Ty>>, Path),
}

#[derive(Clone)]
pub struct Path {
    pub res: Res,
    pub args: Vec<GenericArg>,
    pub bindings: Vec<TypeBinding>,
    pub refine: Vec<RefineArg>,
    pub span: Span,
}

#[derive(Clone)]
pub struct TypeBinding {
    pub ident: SurfaceIdent,
    pub term: Ty,
}

#[derive(Clone)]
pub enum GenericArg {
    Lifetime(Lifetime),
    Type(Ty),
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum Res {
    Def(DefKind, DefId),
    PrimTy(PrimTy),
    SelfTyAlias { alias_to: DefId, is_trait_impl: bool },
    SelfTyParam { trait_: DefId },
}

#[derive(Debug, Clone)]
pub struct RefineParam {
    pub ident: Ident,
    pub sort: Sort,
    pub kind: ParamKind,
    pub fhir_id: FhirId,
    pub span: Span,
}

impl RefineParam {
    pub fn name(&self) -> Name {
        self.ident.name
    }
}

/// How the declared parameter in the surface syntax. This is used to adjust how errors are reported
/// and to control the [inference mode].
///
/// [inference mode]: InferMode
#[derive(Debug, Clone, Copy)]
pub enum ParamKind {
    /// A parameter declared in an explicit scope
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

/// *Infer*ence *mode* for parameter at function calls
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum InferMode {
    /// Generate a fresh evar for the parameter and solve it via syntactic unification. The parameter
    /// must appear at least once as an index for unification to succeed, but otherwise it can appear
    /// (mostly) freely.
    EVar,
    /// Generate a fresh kvar and let fixpoint infer it. This mode can only be used with abstract
    /// refinement predicates. If the parameter is marked as kvar then it can only appear in
    /// positions that result in a _horn_ constraint as required by fixpoint.
    KVar,
}

#[derive(Clone, Copy, TyEncodable, TyDecodable)]
pub enum SortCtor {
    Set,
    Map,
    /// User defined opaque sort
    User {
        name: Symbol,
    },
}

#[derive(Clone, TyEncodable, TyDecodable)]
pub enum Sort {
    Int,
    Bool,
    Real,
    Loc,
    BitVec(usize),
    /// Sort constructor application (e.g. `Set<int>` or `Map<int, int>`)
    App(SortCtor, Vec<Sort>),
    Func(PolyFuncSort),
    /// sort variable
    Var(usize),
    /// A record sort corresponds to the sort associated with a type alias or an adt (struct/enum).
    /// Values of a record sort can be projected using dot notation to extract their fields.
    /// the `List<Sort>` is for the type parameters of (generic) record sorts
    Record(DefId, Vec<Sort>),
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

#[derive(Clone, TyEncodable, TyDecodable)]
pub struct FuncSort {
    /// inputs and output in order
    pub inputs_and_output: Vec<Sort>,
}

#[derive(Clone, TyEncodable, TyDecodable)]
pub struct PolyFuncSort {
    pub params: usize,
    pub fsort: FuncSort,
}

impl PolyFuncSort {
    pub fn new(params: usize, inputs: Vec<Sort>, output: Sort) -> Self {
        let fsort = FuncSort::new(inputs, output);
        Self { params, fsort }
    }
}

#[derive(Clone)]
pub struct Pred {
    pub kind: PredKind,
    pub span: Span,
    pub fhir_id: FhirId,
}

#[derive(Clone)]
pub enum PredKind {
    Expr(Expr),
    Alias(AliasPred, Vec<RefineArg>),
}

#[derive(Clone)]
pub struct AliasPred {
    pub trait_id: DefId,
    pub name: Symbol,
    pub generic_args: Vec<GenericArg>,
}

#[derive(Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub fhir_id: FhirId,
}

#[derive(Clone)]
pub enum ExprKind {
    Const(DefId, Span),
    Var(Ident, Option<ParamKind>),
    Dot(Ident, SurfaceIdent),
    Literal(Lit),
    BinaryOp(BinOp, Box<[Expr; 2]>),
    UnaryOp(UnOp, Box<Expr>),
    App(Func, Vec<Expr>),
    IfThenElse(Box<[Expr; 3]>),
}

#[derive(Clone)]
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

impl PolyTraitRef {
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

impl Ty {
    pub fn as_path(&self) -> Option<&Path> {
        match &self.kind {
            TyKind::BaseTy(bty) => bty.as_path(),
            _ => None,
        }
    }
}

impl BaseTy {
    fn as_path(&self) -> Option<&Path> {
        match &self.kind {
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

impl TryFrom<rustc_hir::def::Res> for Res {
    type Error = ();

    fn try_from(res: rustc_hir::def::Res) -> Result<Self, Self::Error> {
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

impl QPath {
    pub fn span(&self) -> Span {
        match self {
            QPath::Resolved(_, path) => path.span,
        }
    }
}

impl From<QPath> for BaseTy {
    fn from(qpath: QPath) -> Self {
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
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct RefinedBy {
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
    pub index_params: FxIndexMap<Symbol, Sort>,
}

#[derive(Debug)]
pub struct FuncDecl {
    pub name: Symbol,
    pub sort: PolyFuncSort,
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
pub struct Defn {
    pub name: Symbol,
    pub params: usize,
    pub args: Vec<RefineParam>,
    pub sort: Sort,
    pub expr: Expr,
}

impl Generics {
    pub(crate) fn get_param(&self, def_id: LocalDefId) -> &GenericParam {
        self.params.iter().find(|p| p.def_id == def_id).unwrap()
    }

    pub fn with_refined_by(self, refined_by: &RefinedBy) -> Self {
        let mut params = vec![];
        for param in self.params {
            let kind = if refined_by.is_base_generic(param.def_id.to_def_id()) {
                GenericParamKind::SplTy
            } else {
                param.kind
            };
            params.push(GenericParam { def_id: param.def_id, kind });
        }
        Generics { params, ..self }
    }
}

impl RefinedBy {
    pub fn new(
        def_id: LocalDefId,
        index_params: impl IntoIterator<Item = (Symbol, Sort)>,
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

impl Sort {
    pub fn set(t: Sort) -> Self {
        Self::App(SortCtor::Set, vec![t])
    }

    pub fn map(k: Sort, v: Sort) -> Self {
        Self::App(SortCtor::Map, vec![k, v])
    }
}

impl From<PolyFuncSort> for Sort {
    fn from(fsort: PolyFuncSort) -> Self {
        Self::Func(fsort)
    }
}

impl FuncSort {
    pub fn new(mut inputs: Vec<Sort>, output: Sort) -> Self {
        inputs.push(output);
        FuncSort { inputs_and_output: inputs }
    }

    pub fn inputs(&self) -> &[Sort] {
        &self.inputs_and_output[..self.inputs_and_output.len() - 1]
    }

    pub fn output(&self) -> &Sort {
        &self.inputs_and_output[self.inputs_and_output.len() - 1]
    }
}

impl rustc_errors::IntoDiagnosticArg for &Ty {
    fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
        rustc_errors::DiagnosticArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

impl rustc_errors::IntoDiagnosticArg for &Path {
    fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
        rustc_errors::DiagnosticArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

impl GenericArg {
    pub fn expect_type(&self) -> &Ty {
        if let GenericArg::Type(ty) = self {
            ty
        } else {
            bug!("expected `GenericArg::Type`")
        }
    }
}

impl Map {
    pub fn new() -> Self {
        let mut me = Self::default();
        me.insert_theory_funcs();
        me
    }

    pub fn insert_trait(&mut self, def_id: LocalDefId, trait_: Trait) {
        self.traits.insert(def_id, trait_);
    }

    pub fn get_trait(&self, def_id: LocalDefId) -> &Trait {
        self.traits.get(&def_id).unwrap()
    }

    pub fn insert_impl(&mut self, def_id: LocalDefId, impl_: Impl) {
        self.impls.insert(def_id, impl_);
    }

    pub fn get_impl(&self, def_id: LocalDefId) -> &Impl {
        self.impls.get(&def_id).unwrap()
    }

    pub fn insert_assoc_type(&mut self, def_id: LocalDefId, assoc_ty: AssocType) {
        self.assoc_types.insert(def_id, assoc_ty);
    }

    pub fn insert_opaque_tys(&mut self, opaque_tys: UnordMap<LocalDefId, OpaqueTy>) {
        self.opaque_tys.extend_unord(opaque_tys.into_items());
    }

    pub fn get_generics(&self, tcx: TyCtxt, def_id: LocalDefId) -> Option<&Generics> {
        match tcx.def_kind(def_id) {
            DefKind::Struct => Some(&self.get_struct(def_id).generics),
            DefKind::Enum => Some(&self.get_enum(def_id).generics),
            DefKind::Impl { .. } => Some(&self.impls[&def_id].generics),
            DefKind::Trait => Some(&self.traits[&def_id].generics),
            DefKind::TyAlias => Some(&self.type_aliases[&def_id].generics),
            DefKind::AssocTy => Some(&self.assoc_types[&def_id].generics),
            DefKind::Fn => Some(&self.get_fn_sig(def_id).generics),
            DefKind::AssocFn => Some(&self.get_fn_sig(def_id).generics),
            DefKind::OpaqueTy => Some(&self.get_opaque_ty(def_id).generics),
            _ => None,
        }
    }

    pub fn get_opaque_ty(&self, def_id: LocalDefId) -> &OpaqueTy {
        self.opaque_tys.get(&def_id).unwrap()
    }

    // Qualifiers

    pub fn insert_qualifier(&mut self, qualifier: Qualifier) {
        self.flux_items
            .insert(qualifier.name, FluxItem::Qualifier(qualifier));
    }

    pub fn qualifiers(&self) -> impl Iterator<Item = &Qualifier> {
        self.flux_items.values().filter_map(|item| {
            if let FluxItem::Qualifier(qual) = item {
                Some(qual)
            } else {
                None
            }
        })
    }

    // FnSigs

    pub fn insert_fn_sig(&mut self, def_id: LocalDefId, fn_sig: FnSig) {
        self.fns.insert(def_id, fn_sig);
    }

    pub fn insert_fn_quals(&mut self, def_id: LocalDefId, quals: Vec<SurfaceIdent>) {
        self.fn_quals.insert(def_id, quals);
    }

    pub fn add_trusted(&mut self, def_id: LocalDefId) {
        self.trusted.insert(def_id);
    }

    pub fn get_fn_sig(&self, def_id: LocalDefId) -> &FnSig {
        self.fns
            .get(&def_id)
            .unwrap_or_else(|| bug!("no fn_sig found for `{def_id:?}`"))
    }

    pub fn fn_quals(&self) -> impl Iterator<Item = (LocalDefId, &Vec<SurfaceIdent>)> {
        self.fn_quals.iter().map(|(def_id, quals)| (*def_id, quals))
    }

    pub fn get_fn_quals(&self, def_id: LocalDefId) -> impl Iterator<Item = SurfaceIdent> + '_ {
        self.fn_quals
            .get(&def_id)
            .map_or(&[][..], Vec::as_slice)
            .iter()
            .copied()
    }

    pub fn is_trusted(&self, def_id: LocalDefId) -> bool {
        self.trusted.contains(&def_id)
    }

    pub fn insert_extern(&mut self, extern_def_id: DefId, local_def_id: LocalDefId) {
        self.externs.insert(extern_def_id, local_def_id);
    }

    pub fn get_extern(&self, extern_def_id: DefId) -> Option<LocalDefId> {
        self.externs.get(&extern_def_id).copied()
    }

    /// Return whether the local_def_id is a spec for an extern item. This is the inverse of
    /// [`Map::get_extern`]. This currently only works for structs or enums
    pub fn extern_id_of(&self, tcx: TyCtxt, local_def_id: LocalDefId) -> Option<DefId> {
        match tcx.def_kind(local_def_id) {
            DefKind::Struct => self.get_struct(local_def_id).extern_id,
            DefKind::Enum => self.get_enum(local_def_id).extern_id,
            _ => None,
        }
    }

    // ADT

    pub fn insert_refined_by(&mut self, def_id: LocalDefId, refined_by: RefinedBy) {
        self.refined_by.insert(def_id, refined_by);
    }

    pub fn refined_by(&self, def_id: LocalDefId) -> &RefinedBy {
        &self.refined_by[&def_id]
    }

    // Aliases

    pub fn insert_type_alias(&mut self, def_id: LocalDefId, alias: TyAlias) {
        self.type_aliases.insert(def_id, alias);
    }

    pub fn get_type_alias(&self, def_id: impl Borrow<LocalDefId>) -> &TyAlias {
        &self.type_aliases[def_id.borrow()]
    }

    // Structs

    pub fn insert_struct(&mut self, def_id: LocalDefId, struct_def: StructDef) {
        self.structs.insert(def_id, struct_def);
    }

    pub fn get_struct(&self, def_id: impl Borrow<LocalDefId>) -> &StructDef {
        &self.structs[def_id.borrow()]
    }

    // Enums

    pub fn insert_enum(&mut self, def_id: LocalDefId, enum_def: EnumDef) {
        self.enums.insert(def_id, enum_def);
    }

    pub fn get_enum(&self, def_id: impl Borrow<LocalDefId>) -> &EnumDef {
        &self.enums[def_id.borrow()]
    }

    // Consts

    pub fn insert_const(&mut self, c: ConstInfo) {
        self.consts.insert(c.sym, c);
    }

    pub fn consts(&self) -> impl Iterator<Item = &ConstInfo> {
        self.consts.values()
    }

    pub fn const_by_name(&self, name: impl Borrow<Symbol>) -> Option<&ConstInfo> {
        self.consts.get(name.borrow())
    }

    // Theory Symbols
    fn insert_theory_func(
        &mut self,
        name: Symbol,
        fixpoint_name: Symbol,
        params: usize,
        inputs: Vec<Sort>,
        output: Sort,
    ) {
        let sort = PolyFuncSort::new(params, inputs, output);
        self.func_decls
            .insert(name, FuncDecl { name, sort, kind: FuncKind::Thy(fixpoint_name) });
    }

    fn insert_theory_funcs(&mut self) {
        // Bitvector operations
        self.insert_theory_func(
            Symbol::intern("bv_int_to_bv32"),
            Symbol::intern("int_to_bv32"),
            0,
            vec![Sort::Int],
            Sort::BitVec(32),
        );
        self.insert_theory_func(
            Symbol::intern("bv_bv32_to_int"),
            Symbol::intern("bv32_to_int"),
            0,
            vec![Sort::BitVec(32)],
            Sort::Int,
        );
        self.insert_theory_func(
            Symbol::intern("bv_sub"),
            Symbol::intern("bvsub"),
            0,
            vec![Sort::BitVec(32), Sort::BitVec(32)],
            Sort::BitVec(32),
        );
        self.insert_theory_func(
            Symbol::intern("bv_and"),
            Symbol::intern("bvand"),
            0,
            vec![Sort::BitVec(32), Sort::BitVec(32)],
            Sort::BitVec(32),
        );

        // Set operations
        self.insert_theory_func(
            Symbol::intern("set_empty"),
            Symbol::intern("Set_empty"),
            1,
            vec![Sort::Int],
            Sort::set(Sort::Var(0)),
        );
        self.insert_theory_func(
            Symbol::intern("set_singleton"),
            Symbol::intern("Set_sng"),
            1,
            vec![Sort::Var(0)],
            Sort::set(Sort::Var(0)),
        );
        self.insert_theory_func(
            Symbol::intern("set_union"),
            Symbol::intern("Set_cup"),
            1,
            vec![Sort::set(Sort::Var(0)), Sort::set(Sort::Var(0))],
            Sort::set(Sort::Var(0)),
        );
        self.insert_theory_func(
            Symbol::intern("set_is_in"),
            Symbol::intern("Set_mem"),
            1,
            vec![Sort::Var(0), Sort::set(Sort::Var(0))],
            Sort::Bool,
        );

        // Map operations
        self.insert_theory_func(
            Symbol::intern("map_default"),
            Symbol::intern("Map_default"),
            2,
            vec![Sort::Var(1)],
            Sort::map(Sort::Var(0), Sort::Var(1)),
        );
        self.insert_theory_func(
            Symbol::intern("map_select"),
            Symbol::intern("Map_select"),
            2,
            vec![Sort::map(Sort::Var(0), Sort::Var(1)), Sort::Var(0)],
            Sort::Var(1),
        );
        self.insert_theory_func(
            Symbol::intern("map_store"),
            Symbol::intern("Map_store"),
            2,
            vec![Sort::map(Sort::Var(0), Sort::Var(1)), Sort::Var(0), Sort::Var(1)],
            Sort::map(Sort::Var(0), Sort::Var(1)),
        );
    }

    // UIF

    pub fn insert_func_decl(&mut self, symb: Symbol, uif: FuncDecl) {
        self.func_decls.insert(symb, uif);
    }

    pub fn func_decls(&self) -> impl Iterator<Item = &FuncDecl> {
        self.func_decls.values()
    }

    pub fn func_decl(&self, sym: impl Borrow<Symbol>) -> Option<&FuncDecl> {
        self.func_decls.get(sym.borrow())
    }

    // Defn
    pub fn insert_defn(&mut self, symb: Symbol, defn: Defn) {
        self.flux_items.insert(symb, FluxItem::Defn(defn));
    }

    pub fn defns(&self) -> impl Iterator<Item = &Defn> {
        self.flux_items.values().filter_map(|item| {
            if let FluxItem::Defn(defn) = item {
                Some(defn)
            } else {
                None
            }
        })
    }

    pub fn defn(&self, sym: impl Borrow<Symbol>) -> Option<&Defn> {
        self.flux_items.get(sym.borrow()).and_then(|item| {
            if let FluxItem::Defn(defn) = item {
                Some(defn)
            } else {
                None
            }
        })
    }

    // Sorts

    pub fn insert_sort_decl(&mut self, sort_decl: SortDecl) {
        self.sort_decls.insert(sort_decl.name, sort_decl);
    }

    pub fn sort_decls(&self) -> &SortDecls {
        &self.sort_decls
    }

    pub fn get_flux_item(&self, name: impl Borrow<Symbol>) -> Option<&FluxItem> {
        self.flux_items.get(name.borrow())
    }
}

impl StructDef {
    pub fn is_opaque(&self) -> bool {
        matches!(self.kind, StructKind::Opaque)
    }
}

impl fmt::Debug for FnSig {
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

impl fmt::Debug for FnOutput {
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

impl fmt::Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Type(loc, _, ty) => write!(f, "{loc:?}: {ty:?}"),
            Constraint::Pred(e) => write!(f, "{e:?}"),
        }
    }
}

impl fmt::Debug for Ty {
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

impl fmt::Debug for BaseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            BaseTyKind::Path(qpath) => write!(f, "{qpath:?}"),
            BaseTyKind::Slice(ty) => write!(f, "[{ty:?}]"),
        }
    }
}

impl fmt::Debug for QPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QPath::Resolved(_self_ty, path) => {
                write!(f, "{path:?}")
            }
        }
    }
}

impl fmt::Debug for Path {
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

impl fmt::Debug for GenericArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GenericArg::Type(ty) => write!(f, "{ty:?}"),
            GenericArg::Lifetime(lft) => write!(f, "{lft:?}"),
        }
    }
}

impl fmt::Debug for TypeBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} = {:?}", self.ident, self.term)
    }
}

impl fmt::Debug for RefineArg {
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

impl fmt::Debug for AliasPred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{:?} as <{:?}>::{:?}", self.generic_args[0], self.trait_id, self.name)
    }
}

impl fmt::Debug for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            PredKind::Expr(expr) => write!(f, "{expr:?}"),
            PredKind::Alias(alias_pred, refine_args) => {
                write!(f, "{alias_pred:?}({:?})", refine_args.iter().format(", "))
            }
        }
    }
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ExprKind::Var(x, ..) => write!(f, "{x:?}"),
            ExprKind::BinaryOp(op, box [e1, e2]) => write!(f, "({e1:?} {op:?} {e2:?})"),
            ExprKind::UnaryOp(op, e) => write!(f, "{op:?}{e:?}"),
            ExprKind::Literal(lit) => write!(f, "{lit:?}"),
            ExprKind::Const(x, _) => write!(f, "{}", pretty::def_id_to_string(*x)),
            ExprKind::App(uf, es) => write!(f, "{uf:?}({:?})", es.iter().format(", ")),
            ExprKind::IfThenElse(box [p, e1, e2]) => {
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

impl fmt::Debug for Sort {
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

impl fmt::Debug for PolyFuncSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.params > 0 {
            write!(f, "for<{}>{:?}", self.params, self.fsort)
        } else {
            write!(f, "{:?}", self.fsort)
        }
    }
}

impl fmt::Debug for FuncSort {
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
