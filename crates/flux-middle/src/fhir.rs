//! Flux High-Level Intermediate Representation
//!
//! The fhir corresponds to the desugared version of source level flux annotations. The main
//! difference with the surface syntax is that the list of refinement parameters is explicit
//! in fhir. For example, the following signature
//!
//! `fn(x: &strg i32[@n]) ensures x: i32[n + 1]`
//!
//! desugars to
//!
//! `for<n: int, l: loc> fn(&strg<l: i32[n]>) ensures l: i32[n + 1]`.
//!
//! The name fhir is borrowed (pun intended) from rustc's hir to refer to something a bit lower
//! than the surface syntax.

pub mod visit;

use std::{borrow::Cow, fmt};

use flux_common::{bug, span_bug};
use flux_rustc_bridge::def_id_to_string;
use flux_syntax::surface::ParamMode;
pub use flux_syntax::surface::{BinOp, UnOp};
use itertools::Itertools;
use rustc_abi;
pub use rustc_abi::VariantIdx;
use rustc_ast::TraitObjectSyntax;
use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_hash::FxHashMap;
pub use rustc_hir::PrimTy;
use rustc_hir::{
    FnHeader, OwnerId, ParamName, Safety,
    def::{DefKind, Namespace},
    def_id::{DefId, LocalDefId},
};
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable};
pub use rustc_middle::mir::Mutability;
use rustc_middle::{middle::resolve_bound_vars::ResolvedArg, ty::TyCtxt};
use rustc_span::{ErrorGuaranteed, Span, Symbol, symbol::Ident};

use crate::def_id::{FluxDefId, FluxLocalDefId, MaybeExternId};

/// A boolean-like enum used to mark whether a piece of code is ignored.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Ignored {
    Yes,
    No,
}

impl Ignored {
    pub fn to_bool(self) -> bool {
        match self {
            Ignored::Yes => true,
            Ignored::No => false,
        }
    }
}

impl From<bool> for Ignored {
    fn from(value: bool) -> Self {
        if value { Ignored::Yes } else { Ignored::No }
    }
}

/// A boolean-like enum used to mark whether some code should be trusted.
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum Trusted {
    Yes,
    No,
}

impl Trusted {
    pub fn to_bool(self) -> bool {
        match self {
            Trusted::Yes => true,
            Trusted::No => false,
        }
    }
}

impl From<bool> for Trusted {
    fn from(value: bool) -> Self {
        if value { Trusted::Yes } else { Trusted::No }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Generics<'fhir> {
    pub params: &'fhir [GenericParam<'fhir>],
    pub refinement_params: &'fhir [RefineParam<'fhir>],
    pub predicates: Option<&'fhir [WhereBoundPredicate<'fhir>]>,
}

#[derive(Debug, Clone, Copy)]
pub struct GenericParam<'fhir> {
    pub def_id: MaybeExternId,
    pub name: ParamName,
    pub kind: GenericParamKind<'fhir>,
}

#[derive(Debug, Clone, Copy)]
pub enum GenericParamKind<'fhir> {
    Type { default: Option<Ty<'fhir>> },
    Lifetime,
    Const { ty: Ty<'fhir> },
}

#[derive(Debug)]
pub struct Qualifier<'fhir> {
    pub def_id: FluxLocalDefId,
    pub args: &'fhir [RefineParam<'fhir>],
    pub expr: Expr<'fhir>,
    pub global: bool,
}

#[derive(Clone, Copy, Debug)]
pub enum Node<'fhir> {
    Item(&'fhir Item<'fhir>),
    TraitItem(&'fhir TraitItem<'fhir>),
    ImplItem(&'fhir ImplItem<'fhir>),
    OpaqueTy(&'fhir OpaqueTy<'fhir>),
    ForeignItem(&'fhir ForeignItem<'fhir>),
    Ctor,
    AnonConst,
    Expr,
}

impl<'fhir> Node<'fhir> {
    pub fn as_owner(self) -> Option<OwnerNode<'fhir>> {
        match self {
            Node::Item(item) => Some(OwnerNode::Item(item)),
            Node::TraitItem(trait_item) => Some(OwnerNode::TraitItem(trait_item)),
            Node::ImplItem(impl_item) => Some(OwnerNode::ImplItem(impl_item)),
            Node::ForeignItem(foreign_item) => Some(OwnerNode::ForeignItem(foreign_item)),
            Node::OpaqueTy(_) => None,
            Node::AnonConst => None,
            Node::Expr => None,
            Node::Ctor => None,
        }
    }

    pub fn expect_opaque_ty(&self) -> &'fhir OpaqueTy<'fhir> {
        if let Node::OpaqueTy(opaque_ty) = &self { opaque_ty } else { bug!("expected opaque type") }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum OwnerNode<'fhir> {
    Item(&'fhir Item<'fhir>),
    TraitItem(&'fhir TraitItem<'fhir>),
    ImplItem(&'fhir ImplItem<'fhir>),
    ForeignItem(&'fhir ForeignItem<'fhir>),
}

impl<'fhir> OwnerNode<'fhir> {
    pub fn fn_sig(&self) -> Option<&'fhir FnSig<'fhir>> {
        match self {
            OwnerNode::Item(Item { kind: ItemKind::Fn(fn_sig, ..), .. })
            | OwnerNode::TraitItem(TraitItem { kind: TraitItemKind::Fn(fn_sig), .. })
            | OwnerNode::ImplItem(ImplItem { kind: ImplItemKind::Fn(fn_sig), .. })
            | OwnerNode::ForeignItem(ForeignItem {
                kind: ForeignItemKind::Fn(fn_sig, ..), ..
            }) => Some(fn_sig),
            _ => None,
        }
    }

    pub fn generics(self) -> &'fhir Generics<'fhir> {
        match self {
            OwnerNode::Item(item) => &item.generics,
            OwnerNode::TraitItem(trait_item) => &trait_item.generics,
            OwnerNode::ImplItem(impl_item) => &impl_item.generics,
            OwnerNode::ForeignItem(foreign_item) => {
                match foreign_item.kind {
                    ForeignItemKind::Fn(_, generics) => generics,
                }
            }
        }
    }

    pub fn owner_id(&self) -> MaybeExternId<OwnerId> {
        match self {
            OwnerNode::Item(item) => item.owner_id,
            OwnerNode::TraitItem(trait_item) => trait_item.owner_id,
            OwnerNode::ImplItem(impl_item) => impl_item.owner_id,
            OwnerNode::ForeignItem(foreign_item) => foreign_item.owner_id,
        }
    }
}

#[derive(Debug)]
pub struct Item<'fhir> {
    pub owner_id: MaybeExternId<OwnerId>,
    pub generics: Generics<'fhir>,
    pub kind: ItemKind<'fhir>,
}

impl<'fhir> Item<'fhir> {
    pub fn expect_enum(&self) -> &EnumDef<'fhir> {
        if let ItemKind::Enum(enum_def) = &self.kind { enum_def } else { bug!("expected enum") }
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

    pub fn expect_impl(&self) -> &Impl<'fhir> {
        if let ItemKind::Impl(impl_) = &self.kind { impl_ } else { bug!("expected impl") }
    }

    pub fn expect_trait(&self) -> &Trait<'fhir> {
        if let ItemKind::Trait(trait_) = &self.kind { trait_ } else { bug!("expected trait") }
    }
}

#[derive(Debug)]
pub enum ItemKind<'fhir> {
    Enum(EnumDef<'fhir>),
    Struct(StructDef<'fhir>),
    TyAlias(&'fhir TyAlias<'fhir>),
    Trait(Trait<'fhir>),
    Impl(Impl<'fhir>),
    Fn(FnSig<'fhir>),
    Const(Option<Expr<'fhir>>),
}

#[derive(Debug)]
pub struct TraitItem<'fhir> {
    pub owner_id: MaybeExternId<OwnerId>,
    pub generics: Generics<'fhir>,
    pub kind: TraitItemKind<'fhir>,
}

#[derive(Debug)]
pub enum TraitItemKind<'fhir> {
    Fn(FnSig<'fhir>),
    Const,
    Type,
}

#[derive(Debug)]
pub struct ImplItem<'fhir> {
    pub owner_id: MaybeExternId<OwnerId>,
    pub kind: ImplItemKind<'fhir>,
    pub generics: Generics<'fhir>,
}

#[derive(Debug)]
pub enum ImplItemKind<'fhir> {
    Fn(FnSig<'fhir>),
    Const,
    Type,
}

#[derive(Copy, Clone, Debug)]
pub enum FluxItem<'fhir> {
    Qualifier(&'fhir Qualifier<'fhir>),
    Func(&'fhir SpecFunc<'fhir>),
    PrimOpProp(&'fhir PrimOpProp<'fhir>),
}

impl FluxItem<'_> {
    pub fn def_id(self) -> FluxLocalDefId {
        match self {
            FluxItem::Qualifier(qualifier) => qualifier.def_id,
            FluxItem::Func(func) => func.def_id,
            FluxItem::PrimOpProp(prop) => prop.def_id,
        }
    }
}

#[derive(Debug)]
pub struct ForeignItem<'fhir> {
    pub ident: Ident,
    pub kind: ForeignItemKind<'fhir>,
    pub owner_id: MaybeExternId<OwnerId>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ForeignItemKind<'fhir> {
    Fn(FnSig<'fhir>, &'fhir Generics<'fhir>),
}

#[derive(Debug, Clone, Copy)]
pub struct SortDecl {
    pub name: Symbol,
    pub span: Span,
}

pub type SortDecls = FxHashMap<Symbol, SortDecl>;

#[derive(Debug, Clone, Copy)]
pub struct WhereBoundPredicate<'fhir> {
    pub span: Span,
    pub bounded_ty: Ty<'fhir>,
    pub bounds: GenericBounds<'fhir>,
}

pub type GenericBounds<'fhir> = &'fhir [GenericBound<'fhir>];

#[derive(Debug, Clone, Copy)]
pub enum GenericBound<'fhir> {
    Trait(PolyTraitRef<'fhir>),
    Outlives(Lifetime),
}

#[derive(Debug, Clone, Copy)]
pub struct PolyTraitRef<'fhir> {
    pub bound_generic_params: &'fhir [GenericParam<'fhir>],
    /// To represent binders for closures i.e. in Fn* traits; see tests/pos/surface/closure{07,08,09,10}.rs
    pub refine_params: &'fhir [RefineParam<'fhir>],
    pub modifiers: TraitBoundModifier,
    pub trait_ref: Path<'fhir>,
    pub span: Span,
}

#[derive(Debug, Copy, Clone)]
pub enum TraitBoundModifier {
    None,
    Maybe,
}

#[derive(Debug)]
pub struct Trait<'fhir> {
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
    pub body: Option<Expr<'fhir>>,
    pub span: Span,
    pub final_: bool,
}

#[derive(Debug)]
pub struct Impl<'fhir> {
    pub assoc_refinements: &'fhir [ImplAssocReft<'fhir>],
}

impl<'fhir> Impl<'fhir> {
    pub fn find_assoc_reft(&self, name: Symbol) -> Option<&'fhir ImplAssocReft<'fhir>> {
        self.assoc_refinements
            .iter()
            .find(|assoc_reft| assoc_reft.name == name)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ImplAssocReft<'fhir> {
    pub name: Symbol,
    pub params: &'fhir [RefineParam<'fhir>],
    pub output: Sort<'fhir>,
    pub body: Expr<'fhir>,
    pub span: Span,
}

#[derive(Debug)]
pub struct OpaqueTy<'fhir> {
    pub def_id: MaybeExternId,
    pub bounds: GenericBounds<'fhir>,
}

pub type Arena = bumpalo::Bump;

/// A map between rust definitions and flux annotations in their desugared `fhir` form.
///
/// note: most items in this struct have been moved out into their own query or method in genv.
/// We should eventually get rid of this or change its name.
#[derive(Default)]
pub struct FluxItems<'fhir> {
    pub items: FxIndexMap<FluxLocalDefId, FluxItem<'fhir>>,
}

impl FluxItems<'_> {
    pub fn new() -> Self {
        Self { items: Default::default() }
    }
}

#[derive(Debug)]
pub struct TyAlias<'fhir> {
    pub index: Option<RefineParam<'fhir>>,
    pub ty: Ty<'fhir>,
    pub span: Span,
    /// Whether this alias was lifted from a `hir` alias
    pub lifted: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct StructDef<'fhir> {
    pub refinement: &'fhir RefinementKind<'fhir>,
    pub params: &'fhir [RefineParam<'fhir>],
    pub kind: StructKind<'fhir>,
    pub invariants: &'fhir [Expr<'fhir>],
}

#[derive(Debug, Clone, Copy)]
pub enum StructKind<'fhir> {
    Transparent { fields: &'fhir [FieldDef<'fhir>] },
    Opaque,
}

#[derive(Debug, Clone, Copy)]
pub struct FieldDef<'fhir> {
    pub ty: Ty<'fhir>,
    /// Whether this field was lifted from a `hir` field
    pub lifted: bool,
}

#[derive(Debug)]
pub enum RefinementKind<'fhir> {
    /// User specified indices (e.g. length, elems, etc.)
    Refined(RefinedBy<'fhir>),
    /// Singleton refinements e.g. `State[On]`, `State[Off]`
    Reflected,
}

impl RefinementKind<'_> {
    pub fn is_reflected(&self) -> bool {
        matches!(self, RefinementKind::Reflected)
    }
}

#[derive(Debug)]
pub struct EnumDef<'fhir> {
    pub refinement: &'fhir RefinementKind<'fhir>,
    pub params: &'fhir [RefineParam<'fhir>],
    pub variants: &'fhir [VariantDef<'fhir>],
    pub invariants: &'fhir [Expr<'fhir>],
}

#[derive(Debug, Clone, Copy)]
pub struct VariantDef<'fhir> {
    pub def_id: LocalDefId,
    pub params: &'fhir [RefineParam<'fhir>],
    pub fields: &'fhir [FieldDef<'fhir>],
    pub ret: VariantRet<'fhir>,
    pub span: Span,
    /// Whether this variant was lifted from a hir variant
    pub lifted: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct VariantRet<'fhir> {
    pub enum_id: DefId,
    pub idx: Expr<'fhir>,
}

#[derive(Clone, Copy)]
pub struct FnDecl<'fhir> {
    pub requires: &'fhir [Requires<'fhir>],
    pub inputs: &'fhir [Ty<'fhir>],
    pub output: FnOutput<'fhir>,
    pub span: Span,
    /// Whether the sig was lifted from a hir signature
    pub lifted: bool,
}

/// A predicate required to hold before calling a function.
#[derive(Clone, Copy)]
pub struct Requires<'fhir> {
    /// An (optional) list of universally quantified parameters
    pub params: &'fhir [RefineParam<'fhir>],
    pub pred: Expr<'fhir>,
}

#[derive(Clone, Copy)]
pub struct FnSig<'fhir> {
    pub header: FnHeader,
    //// List of local qualifiers for this function
    pub qualifiers: &'fhir [FluxLocalDefId],
    //// List of reveals for this function
    pub reveals: &'fhir [FluxDefId],
    pub decl: &'fhir FnDecl<'fhir>,
}

#[derive(Clone, Copy)]
pub struct FnOutput<'fhir> {
    pub params: &'fhir [RefineParam<'fhir>],
    pub ret: Ty<'fhir>,
    pub ensures: &'fhir [Ensures<'fhir>],
}

#[derive(Clone, Copy)]
pub enum Ensures<'fhir> {
    /// A type constraint on a location
    Type(PathExpr<'fhir>, &'fhir Ty<'fhir>),
    /// A predicate that needs to hold on function exit
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
    Indexed(BaseTy<'fhir>, Expr<'fhir>),
    Exists(&'fhir [RefineParam<'fhir>], &'fhir Ty<'fhir>),
    /// Constrained types `{T | p}` are like existentials but without binders, and are useful
    /// for specifying constraints on indexed values e.g. `{i32[@a] | 0 <= a}`
    Constr(Expr<'fhir>, &'fhir Ty<'fhir>),
    StrgRef(Lifetime, &'fhir PathExpr<'fhir>, &'fhir Ty<'fhir>),
    Ref(Lifetime, MutTy<'fhir>),
    BareFn(&'fhir BareFnTy<'fhir>),
    Tuple(&'fhir [Ty<'fhir>]),
    Array(&'fhir Ty<'fhir>, ConstArg),
    RawPtr(&'fhir Ty<'fhir>, Mutability),
    OpaqueDef(&'fhir OpaqueTy<'fhir>),
    TraitObject(&'fhir [PolyTraitRef<'fhir>], Lifetime, TraitObjectSyntax),
    Never,
    Infer,
    Err(ErrorGuaranteed),
}

pub struct BareFnTy<'fhir> {
    pub safety: Safety,
    pub abi: rustc_abi::ExternAbi,
    pub generic_params: &'fhir [GenericParam<'fhir>],
    pub decl: &'fhir FnDecl<'fhir>,
    pub param_idents: &'fhir [Option<Ident>],
}

#[derive(Clone, Copy)]
pub struct MutTy<'fhir> {
    pub ty: &'fhir Ty<'fhir>,
    pub mutbl: Mutability,
}

/// Our surface syntax doesn't have lifetimes. To deal with them we create a *hole* for every lifetime
/// which we then resolve when we check for structural compatibility against the rust type.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Lifetime {
    /// A lifetime hole created during desugaring.
    Hole(FhirId),
    /// A resolved lifetime created during lifting.
    Resolved(ResolvedArg),
}

/// Owner version of [`FluxLocalDefId`]
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, Encodable, Decodable)]
pub enum FluxOwnerId {
    Flux(FluxLocalDefId),
    Rust(OwnerId),
}

impl FluxOwnerId {
    pub fn def_id(self) -> Option<LocalDefId> {
        match self {
            FluxOwnerId::Flux(_) => None,
            FluxOwnerId::Rust(owner_id) => Some(owner_id.def_id),
        }
    }
}

/// A unique identifier for a node in the AST. Like [`HirId`] it is composed of an `owner` and a
/// `local_id`. We don't generate ids for all nodes, but only for those we need to remember
/// information elaborated during well-formedness checking to later be used during conversion into
/// [`rty`].
///
/// [`rty`]: crate::rty
/// [`HirId`]: rustc_hir::HirId
#[derive(Debug, Hash, PartialEq, Eq, Copy, Clone, Encodable, Decodable)]
pub struct FhirId {
    pub owner: FluxOwnerId,
    pub local_id: ItemLocalId,
}

newtype_index! {
    /// An `ItemLocalId` uniquely identifies something within a given "item-like".
    #[encodable]
    pub struct ItemLocalId {}
}

/// These are types of things that may be refined with indices or existentials
#[derive(Clone, Copy)]
pub struct BaseTy<'fhir> {
    pub kind: BaseTyKind<'fhir>,
    pub fhir_id: FhirId,
    pub span: Span,
}

impl<'fhir> BaseTy<'fhir> {
    pub fn from_qpath(qpath: QPath<'fhir>, fhir_id: FhirId) -> Self {
        let span = qpath.span();
        Self { kind: BaseTyKind::Path(qpath), fhir_id, span }
    }

    fn as_path(&self) -> Option<Path<'fhir>> {
        match self.kind {
            BaseTyKind::Path(QPath::Resolved(None, path)) => Some(path),
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
pub enum BaseTyKind<'fhir> {
    Path(QPath<'fhir>),
    Slice(&'fhir Ty<'fhir>),
    Err(ErrorGuaranteed),
}

#[derive(Clone, Copy)]
pub enum QPath<'fhir> {
    Resolved(Option<&'fhir Ty<'fhir>>, Path<'fhir>),
    TypeRelative(&'fhir Ty<'fhir>, &'fhir PathSegment<'fhir>),
}

#[derive(Clone, Copy)]
pub struct Path<'fhir> {
    pub res: Res,
    pub fhir_id: FhirId,
    pub segments: &'fhir [PathSegment<'fhir>],
    pub refine: &'fhir [Expr<'fhir>],
    pub span: Span,
}

impl<'fhir> Path<'fhir> {
    pub fn last_segment(&self) -> &'fhir PathSegment<'fhir> {
        self.segments.last().unwrap()
    }
}

#[derive(Clone, Copy)]
pub struct PathSegment<'fhir> {
    pub ident: Ident,
    pub res: Res,
    pub args: &'fhir [GenericArg<'fhir>],
    pub constraints: &'fhir [AssocItemConstraint<'fhir>],
}

#[derive(Clone, Copy)]
pub struct AssocItemConstraint<'fhir> {
    pub ident: Ident,
    pub kind: AssocItemConstraintKind<'fhir>,
}

#[derive(Clone, Copy)]
pub enum AssocItemConstraintKind<'fhir> {
    Equality { term: Ty<'fhir> },
}

#[derive(Clone, Copy)]
pub enum GenericArg<'fhir> {
    Lifetime(Lifetime),
    Type(&'fhir Ty<'fhir>),
    Const(ConstArg),
    Infer,
}

impl<'fhir> GenericArg<'fhir> {
    pub fn expect_type(&self) -> &'fhir Ty<'fhir> {
        if let GenericArg::Type(ty) = self { ty } else { bug!("expected `GenericArg::Type`") }
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct ConstArg {
    pub kind: ConstArgKind,
    pub span: Span,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum ConstArgKind {
    Lit(usize),
    Param(DefId),
    Infer,
}

/// The resolution of a path
///
/// The enum contains a subset of the variants in [`rustc_hir::def::Res`] plus some extra variants
/// for extra resolutions found in refinements.
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum Res<Id = !> {
    /// See [`rustc_hir::def::Res::Def`]
    Def(DefKind, DefId),
    /// See [`rustc_hir::def::Res::PrimTy`]
    PrimTy(PrimTy),
    /// See [`rustc_hir::def::Res::SelfTyAlias`]
    SelfTyAlias {
        alias_to: DefId,
        is_trait_impl: bool,
    },
    /// See [`rustc_hir::def::Res::SelfTyParam`]
    SelfTyParam {
        trait_: DefId,
    },
    /// A refinement parameter, e.g., declared with `@n` syntax
    Param(ParamKind, Id),
    /// A refinement function defined with `defs!`
    GlobalFunc(SpecFuncKind),
    Err,
}

/// See [`rustc_hir::def::PartialRes`]
#[derive(Copy, Clone, Debug)]
pub struct PartialRes<Id = !> {
    base_res: Res<Id>,
    unresolved_segments: usize,
}

impl<Id: Copy> PartialRes<Id> {
    pub fn new(base_res: Res<Id>) -> Self {
        Self { base_res, unresolved_segments: 0 }
    }

    pub fn with_unresolved_segments(base_res: Res<Id>, unresolved_segments: usize) -> Self {
        Self { base_res, unresolved_segments }
    }

    #[inline]
    pub fn base_res(&self) -> Res<Id> {
        self.base_res
    }

    pub fn unresolved_segments(&self) -> usize {
        self.unresolved_segments
    }

    #[inline]
    pub fn full_res(&self) -> Option<Res<Id>> {
        (self.unresolved_segments == 0).then_some(self.base_res)
    }

    #[inline]
    pub fn expect_full_res(&self) -> Res<Id> {
        self.full_res().unwrap_or_else(|| bug!("expected full res"))
    }

    pub fn is_box(&self, tcx: TyCtxt) -> bool {
        self.full_res().is_some_and(|res| res.is_box(tcx))
    }

    pub fn map_param_id<R>(&self, f: impl FnOnce(Id) -> R) -> PartialRes<R> {
        PartialRes {
            base_res: self.base_res.map_param_id(f),
            unresolved_segments: self.unresolved_segments,
        }
    }
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

/// How a parameter was declared in the surface syntax.
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum ParamKind {
    /// A parameter declared in an explicit scope, e.g., `fn foo[hdl n: int](x: i32[n])`
    Explicit(Option<ParamMode>),
    /// An implicitly scoped parameter declared with `@a` syntax
    At,
    /// An implicitly scoped parameter declared with `#a` syntax
    Pound,
    /// An implicitly scoped parameter declared with `x: T` syntax.
    Colon,
    /// A location declared with `x: &strg T` syntax.
    Loc,
    /// A parameter introduced with `x: T` syntax that we know *syntactically* is always and error
    /// to use inside a refinement. For example, consider the following:
    /// ```ignore
    /// fn(x: {v. i32[v] | v > 0}) -> i32[x]
    /// ```
    /// In this definition, we know syntactically that `x` binds to a non-base type so it's an error
    /// to use `x` as an index in the return type.
    ///
    /// These parameters should not appear in a desugared item and we only track them during name
    /// resolution to report errors at the use site.
    Error,
}

impl ParamKind {
    pub fn is_loc(&self) -> bool {
        matches!(self, ParamKind::Loc)
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

impl InferMode {
    pub fn from_param_kind(kind: ParamKind) -> InferMode {
        if let ParamKind::Explicit(Some(ParamMode::Horn)) = kind {
            InferMode::KVar
        } else {
            InferMode::EVar
        }
    }

    pub fn prefix_str(self) -> &'static str {
        match self {
            InferMode::EVar => "?",
            InferMode::KVar => "$",
        }
    }
}

#[derive(Clone, Copy)]
pub enum PrimSort {
    Int,
    Bool,
    Char,
    Real,
    Set,
    Map,
    Str,
}

impl PrimSort {
    pub fn name_str(self) -> &'static str {
        match self {
            PrimSort::Int => "int",
            PrimSort::Str => "str",
            PrimSort::Bool => "bool",
            PrimSort::Char => "char",
            PrimSort::Real => "real",
            PrimSort::Set => "Set",
            PrimSort::Map => "Map",
        }
    }

    /// Number of generics expected by this primitive sort
    pub fn generics(self) -> usize {
        match self {
            PrimSort::Int | PrimSort::Bool | PrimSort::Real | PrimSort::Char | PrimSort::Str => 0,
            PrimSort::Set => 1,
            PrimSort::Map => 2,
        }
    }
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
    /// The sort of an associated type in a trait declaration, e.g:
    ///
    /// ```ignore
    /// #[assoc(fn assoc_reft(x: Self::Assoc) -> bool)]
    /// trait MyTrait {
    ///     type Assoc;
    /// }
    /// ```
    SelfParamAssoc { trait_id: DefId, ident: Ident },
    /// The sort automatically generated for an adt (enum/struct) with a `flux::refined_by` annotation
    Adt(DefId),
}

#[derive(Clone, Copy)]
pub enum Sort<'fhir> {
    Path(SortPath<'fhir>),
    /// The sort of a location parameter introduced with the `x: &strg T` syntax.
    Loc,
    /// A bit vector with the given width.
    BitVec(u32),
    /// A polymorphic sort function.
    Func(PolyFuncSort<'fhir>),
    /// The sort associated with a base type. This is normalized into a concrete sort during
    /// conversion
    SortOf(BaseTy<'fhir>),
    /// A sort that needs to be inferred.
    Infer,
    Err(ErrorGuaranteed),
}

/// See [`flux_syntax::surface::SortPath`]
#[derive(Clone, Copy)]
pub struct SortPath<'fhir> {
    pub res: SortRes,
    pub segments: &'fhir [Ident],
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

/// `<qself as path>::name`
#[derive(Clone, Copy)]
pub enum AliasReft<'fhir> {
    /// A fully qualified associated refinement `<qself as trait_>::name`
    Qualified { qself: &'fhir Ty<'fhir>, trait_: Path<'fhir>, name: Ident },
    /// A type-relative associated refinement, e.g., `Self::name`. Note that
    /// we can only resolve this when `ty` is a parameter, similar to how
    /// type-relative associated types are resolved.
    TypeRelative { qself: &'fhir Ty<'fhir>, name: Ident },
}

#[derive(Debug, Clone, Copy)]
pub struct FieldExpr<'fhir> {
    pub ident: Ident,
    pub expr: Expr<'fhir>,
    pub fhir_id: FhirId,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub struct Spread<'fhir> {
    pub expr: Expr<'fhir>,
    pub span: Span,
    pub fhir_id: FhirId,
}

#[derive(Clone, Copy)]
pub struct Expr<'fhir> {
    pub kind: ExprKind<'fhir>,
    pub fhir_id: FhirId,
    pub span: Span,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum QuantKind {
    Forall,
    Exists,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Encodable, Decodable)]
pub struct Range {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Copy)]
pub enum ExprKind<'fhir> {
    Var(QPathExpr<'fhir>),
    Dot(&'fhir Expr<'fhir>, Ident),
    Literal(Lit),
    BinaryOp(BinOp, &'fhir Expr<'fhir>, &'fhir Expr<'fhir>),
    UnaryOp(UnOp, &'fhir Expr<'fhir>),
    App(PathExpr<'fhir>, &'fhir [Expr<'fhir>]),
    /// UIF application representing a primitive operation, e.g. `[<<](x, y)`
    PrimApp(BinOp, &'fhir Expr<'fhir>, &'fhir Expr<'fhir>),
    Alias(AliasReft<'fhir>, &'fhir [Expr<'fhir>]),
    IfThenElse(&'fhir Expr<'fhir>, &'fhir Expr<'fhir>, &'fhir Expr<'fhir>),
    Abs(&'fhir [RefineParam<'fhir>], &'fhir Expr<'fhir>),
    BoundedQuant(QuantKind, RefineParam<'fhir>, Range, &'fhir Expr<'fhir>),
    Record(&'fhir [Expr<'fhir>]),
    Constructor(Option<PathExpr<'fhir>>, &'fhir [FieldExpr<'fhir>], Option<&'fhir Spread<'fhir>>),
    Block(&'fhir [LetDecl<'fhir>], &'fhir Expr<'fhir>),
    Err(ErrorGuaranteed),
}

#[derive(Clone, Copy)]
pub enum QPathExpr<'fhir> {
    Resolved(PathExpr<'fhir>, Option<ParamKind>),
    TypeRelative(&'fhir Ty<'fhir>, Ident),
}

#[derive(Clone, Copy)]
pub struct LetDecl<'fhir> {
    pub param: RefineParam<'fhir>,
    pub init: Expr<'fhir>,
}

impl Expr<'_> {
    pub fn is_colon_param(&self) -> Option<ParamId> {
        if let ExprKind::Var(QPathExpr::Resolved(path, Some(ParamKind::Colon))) = &self.kind
            && let Res::Param(kind, id) = path.res
        {
            debug_assert_eq!(kind, ParamKind::Colon);
            Some(id)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
pub enum NumLitKind {
    Int,
    Real,
}

#[derive(Clone, Copy)]
pub enum Lit {
    Int(u128, Option<NumLitKind>),
    Bool(bool),
    Str(Symbol),
    Char(char),
}

#[derive(Clone, Copy)]
pub struct PathExpr<'fhir> {
    pub segments: &'fhir [Ident],
    pub res: Res<ParamId>,
    pub fhir_id: FhirId,
    pub span: Span,
}

newtype_index! {
    #[debug_format = "a{}"]
    pub struct ParamId {}
}

impl PolyTraitRef<'_> {
    pub fn trait_def_id(&self) -> DefId {
        let path = &self.trait_ref;
        if let Res::Def(DefKind::Trait, did) = path.res {
            did
        } else {
            span_bug!(path.span, "unexpected resolution {:?}", path.res);
        }
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

impl<Id> Res<Id> {
    pub fn descr(&self) -> &'static str {
        match self {
            Res::PrimTy(_) => "builtin type",
            Res::Def(kind, def_id) => kind.descr(*def_id),
            Res::SelfTyAlias { .. } | Res::SelfTyParam { .. } => "self type",
            Res::Param(..) => "refinement parameter",
            Res::GlobalFunc(..) => "refinement function",
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

    /// Returns `None` if this is `Res::Err`
    pub fn ns(&self) -> Option<Namespace> {
        match self {
            Res::Def(kind, ..) => kind.ns(),
            Res::PrimTy(..) | Res::SelfTyAlias { .. } | Res::SelfTyParam { .. } => {
                Some(Namespace::TypeNS)
            }
            Res::Param(..) | Res::GlobalFunc(..) => Some(Namespace::ValueNS),
            Res::Err => None,
        }
    }

    /// Always returns `true` if `self` is `Res::Err`
    pub fn matches_ns(&self, ns: Namespace) -> bool {
        self.ns().is_none_or(|actual_ns| actual_ns == ns)
    }

    pub fn map_param_id<R>(self, f: impl FnOnce(Id) -> R) -> Res<R> {
        match self {
            Res::Param(kind, param_id) => Res::Param(kind, f(param_id)),
            Res::Def(def_kind, def_id) => Res::Def(def_kind, def_id),
            Res::PrimTy(prim_ty) => Res::PrimTy(prim_ty),
            Res::SelfTyAlias { alias_to, is_trait_impl } => {
                Res::SelfTyAlias { alias_to, is_trait_impl }
            }
            Res::SelfTyParam { trait_ } => Res::SelfTyParam { trait_ },
            Res::GlobalFunc(spec_func_kind) => Res::GlobalFunc(spec_func_kind),
            Res::Err => Res::Err,
        }
    }

    pub fn expect_param(self) -> (ParamKind, Id) {
        if let Res::Param(kind, id) = self { (kind, id) } else { bug!("expected param") }
    }
}

impl<Id1, Id2> TryFrom<rustc_hir::def::Res<Id1>> for Res<Id2> {
    type Error = ();

    fn try_from(res: rustc_hir::def::Res<Id1>) -> Result<Self, Self::Error> {
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

impl QPath<'_> {
    pub fn span(&self) -> Span {
        match self {
            QPath::Resolved(_, path) => path.span,
            QPath::TypeRelative(qself, assoc) => qself.span.to(assoc.ident.span),
        }
    }
}

impl Lit {
    pub const TRUE: Lit = Lit::Bool(true);
}

/// Information about the refinement parameters associated with an adt (struct/enum).
#[derive(Clone, Debug)]
pub struct RefinedBy<'fhir> {
    /// When a `#[flux::refined_by(..)]` annotation mentions generic type parameters we implicitly
    /// generate a *polymorphic* data sort.
    ///
    /// For example, if we have:
    /// ```ignore
    /// #[refined_by(keys: Set<K>)]
    /// RMap<K, V> { ... }
    /// ```
    /// we implicitly create a data sort of the form `forall #0. { keys: Set<#0> }`, where `#0` is a
    /// *sort variable*.
    ///
    /// This [`FxIndexSet`] is used to track a mapping between sort variables and their corresponding
    /// type parameter. The [`DefId`] is the id of the type parameter and its index in the set is the
    /// position of the sort variable.
    pub sort_params: FxIndexSet<DefId>,
    /// Fields indexed by their name in the same order they appear in the `#[refined_by(..)]` annotation.
    pub fields: FxIndexMap<Symbol, Sort<'fhir>>,
}

#[derive(Debug)]
pub struct SpecFunc<'fhir> {
    pub def_id: FluxLocalDefId,
    pub params: usize,
    pub args: &'fhir [RefineParam<'fhir>],
    pub sort: Sort<'fhir>,
    pub body: Option<Expr<'fhir>>,
    pub hide: bool,
    pub ident_span: Span,
}
#[derive(Debug)]
pub struct PrimOpProp<'fhir> {
    pub def_id: FluxLocalDefId,
    pub op: BinOp,
    pub args: &'fhir [RefineParam<'fhir>],
    pub body: Expr<'fhir>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpecFuncKind {
    /// Theory symbols *interpreted* by the SMT solver
    Thy(liquid_fixpoint::ThyFunc),
    /// User-defined uninterpreted functions with no definition
    Uif(FluxDefId),
    /// User-defined functions with a body definition
    Def(FluxDefId),
    /// Casts between sorts: id for char, int; if-then-else for bool-int; uninterpreted otherwise.
    Cast,
}

impl SpecFuncKind {
    pub fn def_id(&self) -> Option<FluxDefId> {
        match self {
            SpecFuncKind::Uif(flux_id) | SpecFuncKind::Def(flux_id) => Some(*flux_id),
            _ => None,
        }
    }
}

impl<'fhir> Generics<'fhir> {
    pub fn get_param(&self, def_id: LocalDefId) -> &'fhir GenericParam<'fhir> {
        self.params
            .iter()
            .find(|p| p.def_id.local_id() == def_id)
            .unwrap()
    }
}

impl<'fhir> RefinedBy<'fhir> {
    pub fn new(fields: FxIndexMap<Symbol, Sort<'fhir>>, sort_params: FxIndexSet<DefId>) -> Self {
        RefinedBy { sort_params, fields }
    }

    pub fn trivial() -> Self {
        RefinedBy { sort_params: Default::default(), fields: Default::default() }
    }
}

impl<'fhir> From<PolyFuncSort<'fhir>> for Sort<'fhir> {
    fn from(fsort: PolyFuncSort<'fhir>) -> Self {
        Self::Func(fsort)
    }
}

impl FuncSort<'_> {
    pub fn inputs(&self) -> &[Sort<'_>] {
        &self.inputs_and_output[..self.inputs_and_output.len() - 1]
    }

    pub fn output(&self) -> &Sort<'_> {
        &self.inputs_and_output[self.inputs_and_output.len() - 1]
    }
}

impl rustc_errors::IntoDiagArg for Ty<'_> {
    fn into_diag_arg(self, _path: &mut Option<std::path::PathBuf>) -> rustc_errors::DiagArgValue {
        rustc_errors::DiagArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

impl rustc_errors::IntoDiagArg for Path<'_> {
    fn into_diag_arg(self, _path: &mut Option<std::path::PathBuf>) -> rustc_errors::DiagArgValue {
        rustc_errors::DiagArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

impl StructDef<'_> {
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
        if !self.requires.is_empty() {
            write!(f, "[{:?}] ", self.requires.iter().format(", "))?;
        }
        write!(f, "fn({:?}) -> {:?}", self.inputs.iter().format(", "), self.output)
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

impl fmt::Debug for Requires<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.params.is_empty() {
            write!(
                f,
                "forall {}.",
                self.params.iter().format_with(",", |param, f| {
                    f(&format_args!("{}:{:?}", param.name, param.sort))
                })
            )?;
        }
        write!(f, "{:?}", self.pred)
    }
}

impl fmt::Debug for Ensures<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ensures::Type(loc, ty) => write!(f, "{loc:?}: {ty:?}"),
            Ensures::Pred(e) => write!(f, "{e:?}"),
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
            TyKind::StrgRef(_lft, loc, ty) => write!(f, "&strg <{loc:?}: {ty:?}>"),
            TyKind::Ref(_lft, mut_ty) => {
                write!(f, "&{}{:?}", mut_ty.mutbl.prefix_str(), mut_ty.ty)
            }
            TyKind::BareFn(bare_fn_ty) => {
                write!(f, "{bare_fn_ty:?}")
            }
            TyKind::Tuple(tys) => write!(f, "({:?})", tys.iter().format(", ")),
            TyKind::Array(ty, len) => write!(f, "[{ty:?}; {len:?}]"),
            TyKind::Never => write!(f, "!"),
            TyKind::Constr(pred, ty) => write!(f, "{{{ty:?} | {pred:?}}}"),
            TyKind::RawPtr(ty, Mutability::Not) => write!(f, "*const {ty:?}"),
            TyKind::RawPtr(ty, Mutability::Mut) => write!(f, "*mut {ty:?}"),
            TyKind::Infer => write!(f, "_"),
            TyKind::OpaqueDef(opaque_ty) => {
                write!(f, "impl trait <def_id = {:?}>", opaque_ty.def_id.resolved_id(),)
            }
            TyKind::TraitObject(poly_traits, _lft, _syntax) => {
                write!(f, "dyn {poly_traits:?}")
            }
            TyKind::Err(_) => write!(f, "err"),
        }
    }
}

impl fmt::Debug for BareFnTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.generic_params.is_empty() {
            write!(
                f,
                "for<{}>",
                self.generic_params
                    .iter()
                    .map(|param| param.name.ident())
                    .format(",")
            )?;
        }
        write!(f, "{:?}", self.decl)
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

impl fmt::Debug for ConstArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

impl fmt::Debug for ConstArgKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstArgKind::Lit(n) => write!(f, "{n}"),
            ConstArgKind::Param(p) => write!(f, "{p:?}"),
            ConstArgKind::Infer => write!(f, "_"),
        }
    }
}

impl fmt::Debug for BaseTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            BaseTyKind::Path(qpath) => write!(f, "{qpath:?}"),
            BaseTyKind::Slice(ty) => write!(f, "[{ty:?}]"),
            BaseTyKind::Err(_) => write!(f, "err"),
        }
    }
}

impl fmt::Debug for QPath<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QPath::Resolved(_, path) => write!(f, "{path:?}"),
            QPath::TypeRelative(qself, assoc) => write!(f, "<{qself:?}>::{assoc:?}"),
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
            .chain(self.constraints.iter().map(|b| b as &dyn std::fmt::Debug))
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
            GenericArg::Const(cst) => write!(f, "{cst:?}"),
            GenericArg::Infer => write!(f, "_"),
        }
    }
}

impl fmt::Debug for AssocItemConstraint<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            AssocItemConstraintKind::Equality { term } => {
                write!(f, "{:?} = {:?}", self.ident, term)
            }
        }
    }
}

impl fmt::Debug for AliasReft<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AliasReft::Qualified { qself, trait_, name } => {
                write!(f, "<{qself:?} as {trait_:?}>::{name}")
            }
            AliasReft::TypeRelative { qself, name } => {
                write!(f, "{qself:?}::{name}")
            }
        }
    }
}

impl fmt::Debug for QuantKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QuantKind::Forall => write!(f, "∀"),
            QuantKind::Exists => write!(f, "∃"),
        }
    }
}

impl fmt::Debug for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ExprKind::Var(QPathExpr::Resolved(path, ..)) => write!(f, "{path:?}"),
            ExprKind::Var(QPathExpr::TypeRelative(qself, assoc)) => {
                write!(f, "<{qself:?}>::{assoc}")
            }
            ExprKind::BinaryOp(op, e1, e2) => write!(f, "({e1:?} {op:?} {e2:?})"),
            ExprKind::PrimApp(op, e1, e2) => write!(f, "[{op:?}]({e1:?}, {e2:?})"),
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
            ExprKind::Abs(params, body) => {
                write!(
                    f,
                    "|{}| {body:?}",
                    params.iter().format_with(", ", |param, f| {
                        f(&format_args!("{}: {:?}", param.name, param.sort))
                    })
                )
            }
            ExprKind::Record(flds) => {
                write!(f, "{{ {:?} }}", flds.iter().format(", "))
            }
            ExprKind::Constructor(path, exprs, spread) => {
                if let Some(path) = path
                    && let Some(s) = spread
                {
                    write!(f, "{:?} {{ {:?}, ..{:?} }}", path, exprs.iter().format(", "), s)
                } else if let Some(path) = path {
                    write!(f, "{:?} {{ {:?} }}", path, exprs.iter().format(", "))
                } else if let Some(s) = spread {
                    write!(f, "{{ {:?} ..{:?} }}", exprs.iter().format(", "), s)
                } else {
                    write!(f, "{{ {:?} }}", exprs.iter().format(", "))
                }
            }
            ExprKind::BoundedQuant(kind, refine_param, rng, expr) => {
                write!(f, "{kind:?} {refine_param:?} in {}.. {} {{ {expr:?} }}", rng.start, rng.end)
            }
            ExprKind::Err(_) => write!(f, "err"),
            ExprKind::Block(decls, body) => {
                for decl in decls {
                    write!(f, "let {:?} = {:?};", decl.param, decl.init)?;
                }
                write!(f, "{body:?}")
            }
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
            Lit::Int(i, Some(NumLitKind::Real)) => write!(f, "{i}real"),
            Lit::Int(i, _) => write!(f, "{i}"),
            Lit::Bool(b) => write!(f, "{b}"),
            Lit::Str(s) => write!(f, "\"{s:?}\""),
            Lit::Char(c) => write!(f, "\'{c}\'"),
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
            Sort::SortOf(bty) => write!(f, "<{bty:?}>::sort"),
            Sort::Infer => write!(f, "_"),
            Sort::Err(_) => write!(f, "err"),
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
            SortRes::PrimSort(PrimSort::Char) => write!(f, "char"),
            SortRes::PrimSort(PrimSort::Str) => write!(f, "str"),
            SortRes::PrimSort(PrimSort::Set) => write!(f, "Set"),
            SortRes::PrimSort(PrimSort::Map) => write!(f, "Map"),
            SortRes::SortParam(n) => write!(f, "@{n}"),
            SortRes::TyParam(def_id) => write!(f, "{}::sort", def_id_to_string(*def_id)),
            SortRes::SelfParam { trait_id } => {
                write!(f, "{}::Self::sort", def_id_to_string(*trait_id))
            }
            SortRes::SelfAlias { alias_to } => {
                write!(f, "{}::Self::sort", def_id_to_string(*alias_to))
            }
            SortRes::SelfParamAssoc { ident: assoc, .. } => {
                write!(f, "Self::{assoc}")
            }
            SortRes::User { name } => write!(f, "{name}"),
            SortRes::Adt(def_id) => write!(f, "{}::sort", def_id_to_string(*def_id)),
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
