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
pub use flux_syntax::surface::{BinOp, UnOp};
use itertools::Itertools;
use rustc_data_structures::{
    fx::{FxIndexMap, FxIndexSet},
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
    Base,
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

#[derive(Clone, Copy)]
pub enum Node<'fhir> {
    Item(&'fhir Item<'fhir>),
    TraitItem(&'fhir TraitItem<'fhir>),
    ImplItem(&'fhir ImplItem<'fhir>),
}

impl<'fhir> Node<'fhir> {
    pub fn fn_sig(&self) -> Option<&'fhir FnSig<'fhir>> {
        match self {
            Node::Item(Item { kind: ItemKind::Fn(fn_sig, ..), .. })
            | Node::TraitItem(TraitItem { kind: TraitItemKind::Fn(fn_sig), .. })
            | Node::ImplItem(ImplItem { kind: ImplItemKind::Fn(fn_sig), .. }) => Some(fn_sig),
            _ => None,
        }
    }

    pub fn generics(self) -> &'fhir Generics<'fhir> {
        match self {
            Node::Item(item) => item.generics(),
            Node::TraitItem(trait_item) => trait_item.generics(),
            Node::ImplItem(impl_item) => impl_item.generics(),
        }
    }
}

pub struct Item<'fhir> {
    pub owner_id: OwnerId,
    pub kind: ItemKind<'fhir>,
}

impl<'fhir> Item<'fhir> {
    pub fn generics(&self) -> &Generics<'fhir> {
        match &self.kind {
            ItemKind::Enum(enum_def) => &enum_def.generics,
            ItemKind::Struct(struct_def) => &struct_def.generics,
            ItemKind::TyAlias(ty_alias) => &ty_alias.generics,
            ItemKind::Trait(trait_) => &trait_.generics,
            ItemKind::Impl(impl_) => &impl_.generics,
            ItemKind::Fn(fn_sig) => &fn_sig.decl.generics,
            ItemKind::OpaqueTy(opaque_ty) => &opaque_ty.generics,
        }
    }

    pub fn expect_enum(&self) -> &EnumDef<'fhir> {
        if let ItemKind::Enum(enum_def) = &self.kind {
            enum_def
        } else {
            bug!("expected enum")
        }
    }

    pub fn expect_struct(&self) -> &StructDef<'fhir> {
        if let ItemKind::Struct(struct_def) = &self.kind {
            struct_def
        } else {
            bug!("expected struct")
        }
    }

    pub fn expect_type_alias(&self) -> &TyAlias<'fhir> {
        if let ItemKind::TyAlias(ty_alias) = &self.kind {
            ty_alias
        } else {
            bug!("expected type alias")
        }
    }

    pub fn expect_opaque_ty(&self) -> &OpaqueTy<'fhir> {
        if let ItemKind::OpaqueTy(opaque_ty) = &self.kind {
            opaque_ty
        } else {
            bug!("expected opaque type")
        }
    }

    pub fn expect_impl(&self) -> &Impl<'fhir> {
        if let ItemKind::Impl(impl_) = &self.kind {
            impl_
        } else {
            bug!("expected impl")
        }
    }
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
    pub owner_id: OwnerId,
    pub kind: TraitItemKind<'fhir>,
}

impl<'fhir> TraitItem<'fhir> {
    pub fn generics(&self) -> &Generics<'fhir> {
        match &self.kind {
            TraitItemKind::Fn(fn_sig) => &fn_sig.decl.generics,
            TraitItemKind::Type(assoc_ty) => &assoc_ty.generics,
        }
    }
}

pub enum TraitItemKind<'fhir> {
    Fn(FnSig<'fhir>),
    Type(AssocType<'fhir>),
}

pub struct ImplItem<'fhir> {
    pub owner_id: OwnerId,
    pub kind: ImplItemKind<'fhir>,
}

impl<'fhir> ImplItem<'fhir> {
    pub fn generics(&self) -> &Generics<'fhir> {
        match &self.kind {
            ImplItemKind::Fn(fn_sig) => &fn_sig.decl.generics,
            ImplItemKind::Type(assoc_type) => &assoc_type.generics,
        }
    }
}

pub enum ImplItemKind<'fhir> {
    Fn(FnSig<'fhir>),
    Type(AssocType<'fhir>),
}

#[derive(Debug)]
pub enum FluxItem<'fhir> {
    Qualifier(Qualifier<'fhir>),
    Func(SpecFunc<'fhir>),
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
    pub assoc_refinements: &'fhir [TraitAssocReft<'fhir>],
}

impl<'fhir> Trait<'fhir> {
    pub fn find_assoc_reft(&self, name: Symbol) -> Option<&'fhir TraitAssocReft<'fhir>> {
        self.assoc_refinements
            .iter()
            .find(|assoc_reft| assoc_reft.name == name)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TraitAssocReft<'fhir> {
    pub name: Symbol,
    pub params: &'fhir [RefineParam<'fhir>],
    pub output: Sort<'fhir>,
    pub span: Span,
}

pub struct Impl<'fhir> {
    pub generics: Generics<'fhir>,
    pub assoc_refinements: &'fhir [ImplAssocReft<'fhir>],
    /// Whether this is a wrapper for an extern impl
    pub extern_id: Option<DefId>,
}

impl<'fhir> Impl<'fhir> {
    pub fn find_assoc_reft(&self, name: Symbol) -> Option<&'fhir ImplAssocReft<'fhir>> {
        self.assoc_refinements
            .iter()
            .find(|assoc_reft| assoc_reft.name == name)
    }
}

#[derive(Clone, Copy)]
pub struct ImplAssocReft<'fhir> {
    pub name: Symbol,
    pub params: &'fhir [RefineParam<'fhir>],
    pub output: Sort<'fhir>,
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
pub struct FnDecl<'fhir> {
    pub generics: Generics<'fhir>,
    /// example: vec![(0 <= n), (l: i32)]
    pub requires: &'fhir [Constraint<'fhir>],
    /// example: vec![(x: StrRef(l))]
    pub args: &'fhir [Ty<'fhir>],
    pub output: FnOutput<'fhir>,
    pub span: Span,
    /// Whether the sig was [lifted] from a hir signature
    ///
    /// [lifted]: lift::LiftCtxt::lift_fn_decl
    pub lifted: bool,
}

#[derive(Clone, Copy)]
pub struct FnSig<'fhir> {
    pub trusted: bool,
    //// List of local qualifiers for this function
    pub qualifiers: &'fhir [SurfaceIdent],
    pub decl: &'fhir FnDecl<'fhir>,
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
    Type(PathExpr<'fhir>, Ty<'fhir>),
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
    /// of kind [type]. We cannot distinguish these syntactially so we resolve them later in the
    /// analysis.
    ///
    /// [existential]: crate::rty::TyKind::Exists
    /// [type]: GenericParamKind::Type
    BaseTy(BaseTy<'fhir>),
    Indexed(BaseTy<'fhir>, RefineArg<'fhir>),
    Exists(&'fhir [RefineParam<'fhir>], &'fhir Ty<'fhir>),
    /// Constrained types `{T | p}` are like existentials but without binders, and are useful
    /// for specifying constraints on indexed values e.g. `{i32[@a] | 0 <= a}`
    Constr(Expr<'fhir>, &'fhir Ty<'fhir>),
    Ptr(Lifetime, PathExpr<'fhir>),
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
    pub fn is_colon_param(&self) -> Option<ParamId> {
        if let RefineArgKind::Expr(expr) = &self.kind
            && let ExprKind::Var(path, Some(ParamKind::Colon)) = &expr.kind
            && let ExprRes::Param(kind, id) = path.res
        {
            debug_assert_eq!(kind, ParamKind::Colon);
            Some(id)
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
    pub segments: &'fhir [PathSegment<'fhir>],
    pub refine: &'fhir [RefineArg<'fhir>],
    pub span: Span,
}

impl<'fhir> Path<'fhir> {
    pub fn last_segment(&self) -> &'fhir PathSegment<'fhir> {
        self.segments.last().unwrap()
    }
}

#[derive(Clone, Copy)]
pub struct PathSegment<'fhir> {
    pub ident: SurfaceIdent,
    pub res: Res,
    pub args: &'fhir [GenericArg<'fhir>],
    pub bindings: &'fhir [TypeBinding<'fhir>],
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
    Err,
}

#[derive(Debug, Clone, Copy)]
pub struct RefineParam<'fhir> {
    pub id: ParamId,
    pub name: Symbol,
    pub span: Span,
    pub sort: Sort<'fhir>,
    pub kind: ParamKind,
    pub fhir_id: FhirId,
}

/// How the parameter was declared in the surface syntax. This is used to adjust how errors are
/// reported and to control the [inference mode].
///
/// [inference mode]: InferMode
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum ParamKind {
    /// A parameter declared in an explicit scope, e.g., `fn foo<refine n: int>(x: i32[n])`
    Explicit,
    /// An implicitly scoped parameter declared with `@a` syntax
    At,
    /// An implicitly scoped parameter declared with `#a` syntax
    Pound,
    /// An implicitly scoped parameter declared with `x: T` syntax.
    Colon,
    /// A location declared with `x: &strg T` syntax, the `usize` is the position in the list of
    /// arguments.
    Loc(usize),
    /// A parameter introduced with `x: T` syntax that we know *syntactically* is always and error
    /// to used inside a refinement. For example, consider the following:
    /// ```ignore
    /// fn(x: {v. i32[v] | v > 0}) -> i32[x]
    /// ```
    /// In this definition, we know syntatically that `x` binds to a non-base type so it's an error
    /// to use `x` as an index in the return type.
    ///
    /// These parameters should not appear in a desugared item and we only track them during name
    /// resolution to report errors at the use site.
    Error,
}

impl ParamKind {
    pub(crate) fn is_implicit(&self) -> bool {
        matches!(self, ParamKind::At | ParamKind::Pound | ParamKind::Colon)
    }

    pub fn is_loc(&self) -> bool {
        matches!(self, ParamKind::Loc(_))
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
pub enum PrimSort {
    Int,
    Bool,
    Real,
    Set,
    Map,
}

#[derive(Clone, Copy)]
pub enum SortRes {
    /// A primitive sort.
    PrimSort(PrimSort),
    /// A user declared sort.
    User { name: Symbol },
    /// A sort parameter inside a polymorphic function or data sort.
    SortParam(usize),
    /// The sort associated to a (generic) type parameter
    TyParam(DefId),
    /// The sort of the `Self` type, as used within a trait.
    SelfParam {
        /// The trait this `Self` is a generic parameter for.
        trait_id: DefId,
    },
    /// The sort of a `Self` type, as used somewhere other than within a trait.
    SelfAlias {
        /// The item introducing the `Self` type alias, e.g., an impl block.
        alias_to: DefId,
    },
    /// The sort of an adt (enum/struct) or type alias.
    Adt(DefId),
}

#[derive(Clone, Copy)]
pub enum Sort<'fhir> {
    Path(SortPath<'fhir>),
    /// The sort of a location parameter introduced with the `x: &strg T` syntax.
    Loc,
    /// A bit vector with the given width.
    BitVec(usize),
    /// A polymorphic sort function.
    Func(PolyFuncSort<'fhir>),
    /// A sort that needs to be inferred.
    Infer,
}

/// See [`flux_syntax::surface::SortPath`]
#[derive(Clone, Copy)]
pub struct SortPath<'fhir> {
    pub res: SortRes,
    pub segment: SurfaceIdent,
    pub args: &'fhir [Sort<'fhir>],
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
pub struct AliasReft<'fhir> {
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
    Var(PathExpr<'fhir>, Option<ParamKind>),
    Dot(PathExpr<'fhir>, SurfaceIdent),
    Literal(Lit),
    BinaryOp(BinOp, &'fhir Expr<'fhir>, &'fhir Expr<'fhir>),
    UnaryOp(UnOp, &'fhir Expr<'fhir>),
    App(PathExpr<'fhir>, &'fhir [Expr<'fhir>]),
    Alias(AliasReft<'fhir>, &'fhir [Expr<'fhir>]),
    IfThenElse(&'fhir Expr<'fhir>, &'fhir Expr<'fhir>, &'fhir Expr<'fhir>),
}

#[derive(Clone, Copy)]
pub enum Lit {
    Int(i128),
    Real(i128),
    Bool(bool),
}

pub type SurfaceIdent = rustc_span::symbol::Ident;

#[derive(Clone, Copy, Debug)]
pub enum ExprRes<Id = ParamId> {
    Param(ParamKind, Id),
    Const(DefId),
    NumConst(i128),
    GlobalFunc(SpecFuncKind, Symbol),
}

impl<Id> ExprRes<Id> {
    pub fn expect_param(self) -> (ParamKind, Id) {
        if let ExprRes::Param(kind, id) = self {
            (kind, id)
        } else {
            bug!("expected param")
        }
    }

    pub fn expect_loc_param(self) -> (usize, Id) {
        if let ExprRes::Param(ParamKind::Loc(idx), id) = self {
            (idx, id)
        } else {
            bug!("expected loc")
        }
    }
}

#[derive(Clone, Copy)]
pub struct PathExpr<'fhir> {
    pub segments: &'fhir [SurfaceIdent],
    pub res: ExprRes,
    pub fhir_id: FhirId,
    pub span: Span,
}

newtype_index! {
    #[debug_format = "a{}"]
    pub struct ParamId {}
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
            Res::Err => "unresolved item",
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
            rustc_hir::def::Res::Err => Ok(Res::Err),
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

impl Lit {
    pub const TRUE: Lit = Lit::Bool(true);
}

/// Information about the refinement parameters associated with a type alias or a struct/enum.
#[derive(Clone, Debug)]
pub struct RefinedBy<'fhir> {
    pub span: Span,
    /// Tracks the mapping from bound var to generic def ids. e.g. if we have
    ///
    /// ```ignore
    /// #[refined_by(keys: Set<K>)]
    /// RMap<K, V> { ...}
    /// ```
    /// then the sort associated to `RMap` is of the form `forall #0. { keys: Set<#0> }`
    /// and `sort_params` will be `vec![K]`,  i.e., it maps `Var(0)` to `K`.
    pub sort_params: FxIndexSet<DefId>,
    /// Index parameters indexed by their name and in the same order they appear in the definition.
    pub index_params: FxIndexMap<Symbol, Sort<'fhir>>,
}

#[derive(Debug)]
pub struct SpecFunc<'fhir> {
    pub name: Symbol,
    pub params: usize,
    pub args: &'fhir [RefineParam<'fhir>],
    pub sort: Sort<'fhir>,
    pub body: Option<Expr<'fhir>>,
}

#[derive(Debug)]
pub struct SpecFuncDecl<'fhir> {
    pub name: Symbol,
    pub sort: PolyFuncSort<'fhir>,
    pub kind: SpecFuncKind,
}

#[derive(Debug, Clone, Copy, TyEncodable, TyDecodable, PartialEq, Eq, Hash)]
pub enum SpecFuncKind {
    /// Theory symbols "interpreted" by the SMT solver: `Symbol` is Fixpoint's name for the operation e.g. `set_cup` for flux's `set_union`
    Thy(Symbol),
    /// User-defined uninterpreted functions with no definition
    Uif,
    /// User-defined functions with a body definition
    Def,
}

impl<'fhir> Generics<'fhir> {
    pub(crate) fn get_param(&self, def_id: LocalDefId) -> &'fhir GenericParam<'fhir> {
        self.params.iter().find(|p| p.def_id == def_id).unwrap()
    }

    pub fn with_refined_by(self, genv: GlobalEnv<'fhir, '_>, refined_by: &RefinedBy) -> Self {
        let params = genv.alloc_slice_fill_iter(self.params.iter().map(|param| {
            let kind = if refined_by.is_base_generic(param.def_id.to_def_id()) {
                GenericParamKind::Base
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
        index_params: impl IntoIterator<Item = (Symbol, Sort<'fhir>)>,
        sort_params: FxIndexSet<DefId>,
        span: Span,
    ) -> Self {
        let index_params: FxIndexMap<_, _> = index_params.into_iter().collect();
        RefinedBy { span, sort_params, index_params }
    }

    pub fn trivial(span: Span) -> Self {
        RefinedBy { sort_params: Default::default(), span, index_params: Default::default() }
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
        write!(f, "{:?}", self.decl)
    }
}

impl fmt::Debug for FnDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.generics.refinement_params.is_empty() {
            write!(
                f,
                "for<{}> ",
                self.generics
                    .refinement_params
                    .iter()
                    .format_with(", ", |param, f| {
                        f(&format_args!("{}: {:?}", param.name, param.sort))
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
                    f(&format_args!("{}: {:?}", param.name, param.sort))
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
            Constraint::Type(loc, ty) => write!(f, "{loc:?}: {ty:?}"),
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
                        f(&format_args!("{}:{:?}", param.name, param.sort))
                    })
                )?;
                if let TyKind::Constr(pred, ty) = &ty.kind {
                    write!(f, ". {ty:?} | {pred:?}}}")
                } else {
                    write!(f, ". {ty:?}}}")
                }
            }
            TyKind::Ptr(lft, loc) => write!(f, "ptr<{lft:?}, {loc:?}>"),
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
        write!(f, "{:?}", self.segments.iter().format("::"))?;
        if !self.refine.is_empty() {
            write!(f, "({:?})", self.refine.iter().format(", "))?;
        }
        Ok(())
    }
}

impl fmt::Debug for PathSegment<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ident)?;
        let args: Vec<_> = self
            .args
            .iter()
            .map(|a| a as &dyn std::fmt::Debug)
            .chain(self.bindings.iter().map(|b| b as &dyn std::fmt::Debug))
            .collect();
        if !args.is_empty() {
            write!(f, "<{:?}>", args.iter().format(", "))?;
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
                        f(&format_args!("{}: {:?}", param.name, param.sort))
                    })
                )
            }
            RefineArgKind::Record(flds) => {
                write!(f, "{{ {:?} }}", flds.iter().format(", "))
            }
        }
    }
}

impl fmt::Debug for AliasReft<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let [self_ty, rest @ ..] = self.generic_args else {
            bug!("expected at least one argument")
        };
        write!(f, "<{:?} as {}", self_ty, pretty::def_id_to_string(self.trait_id))?;
        if !rest.is_empty() {
            write!(f, "<{:?}>", rest.iter().format(", "))?;
        }
        write!(f, ">::{}", self.name)
    }
}

impl fmt::Debug for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ExprKind::Var(x, ..) => write!(f, "{x:?}"),
            ExprKind::BinaryOp(op, e1, e2) => write!(f, "({e1:?} {op:?} {e2:?})"),
            ExprKind::UnaryOp(op, e) => write!(f, "{op:?}{e:?}"),
            ExprKind::Literal(lit) => write!(f, "{lit:?}"),
            ExprKind::App(uf, es) => write!(f, "{uf:?}({:?})", es.iter().format(", ")),
            ExprKind::Alias(alias, refine_args) => {
                write!(f, "{alias:?}({:?})", refine_args.iter().format(", "))
            }
            ExprKind::IfThenElse(p, e1, e2) => {
                write!(f, "(if {p:?} {{ {e1:?} }} else {{ {e2:?} }})")
            }
            ExprKind::Dot(var, fld) => write!(f, "{var:?}.{fld}"),
        }
    }
}

impl fmt::Debug for PathExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.segments.iter().format("::"))
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

impl fmt::Debug for Sort<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Path(path) => write!(f, "{path:?}"),
            Sort::BitVec(w) => write!(f, "bitvec({w})"),
            Sort::Loc => write!(f, "loc"),
            Sort::Func(fsort) => write!(f, "{fsort:?}"),
            Sort::Infer => write!(f, "_"),
        }
    }
}

impl fmt::Debug for SortPath<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.res)?;
        if !self.args.is_empty() {
            write!(f, "<{:?}>", self.args.iter().format(", "))?;
        }
        Ok(())
    }
}

impl fmt::Debug for SortRes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SortRes::PrimSort(PrimSort::Bool) => write!(f, "bool"),
            SortRes::PrimSort(PrimSort::Int) => write!(f, "int"),
            SortRes::PrimSort(PrimSort::Real) => write!(f, "real"),
            SortRes::PrimSort(PrimSort::Set) => write!(f, "Set"),
            SortRes::PrimSort(PrimSort::Map) => write!(f, "Map"),
            SortRes::SortParam(n) => write!(f, "@{}", n),
            SortRes::TyParam(def_id) => write!(f, "sortof({})", pretty::def_id_to_string(*def_id)),
            SortRes::SelfParam { trait_id } => {
                write!(f, "sortof({}::Self)", pretty::def_id_to_string(*trait_id))
            }
            SortRes::SelfAlias { alias_to } => {
                write!(f, "sortof({}::Self)", pretty::def_id_to_string(*alias_to))
            }
            SortRes::User { name } => write!(f, "{name}"),
            SortRes::Adt(def_id) => write!(f, "{}::Sort", pretty::def_id_to_string(*def_id)),
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
