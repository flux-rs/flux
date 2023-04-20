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

use std::{
    borrow::{Borrow, Cow},
    fmt,
};

pub use flux_fixpoint::{BinOp, UnOp};
use itertools::Itertools;
use rustc_ast::Mutability;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hash::{FxHashMap, FxHashSet};
pub use rustc_hir::PrimTy;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    OwnerId,
};
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable, TyDecodable, TyEncodable};
use rustc_span::{Span, Symbol};
pub use rustc_target::abi::VariantIdx;

use crate::{
    intern::{impl_internable, List},
    pretty,
    rty::Constant,
};

#[derive(Debug)]
pub struct Generics {
    pub params: Vec<GenericParamDef>,
}

#[derive(Debug)]
pub struct GenericParamDef {
    pub def_id: LocalDefId,
    pub kind: GenericParamDefKind,
}

#[derive(Debug)]
pub enum GenericParamDefKind {
    Type { default: Option<Ty> },
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

/// A map between rust definitions and flux annotations in their desugared `fhir` form.
///
/// note: `Map` is a very generic name, so we typically use the type qualified as `fhir::Map`.
#[derive(Default, Debug)]
pub struct Map {
    generics: FxHashMap<LocalDefId, Generics>,
    func_decls: FxHashMap<Symbol, FuncDecl>,
    sort_decls: FxHashMap<Symbol, SortDecl>,
    flux_items: FxHashMap<Symbol, FluxItem>,
    consts: FxHashMap<Symbol, ConstInfo>,
    refined_by: FxHashMap<LocalDefId, RefinedBy>,
    type_aliases: FxHashMap<LocalDefId, TyAlias>,
    structs: FxHashMap<LocalDefId, StructDef>,
    enums: FxHashMap<LocalDefId, EnumDef>,
    fns: FxHashMap<LocalDefId, FnSig>,
    fn_quals: FxHashMap<LocalDefId, Vec<SurfaceIdent>>,
    trusted: FxHashSet<LocalDefId>,
    externs: FxHashMap<DefId, LocalDefId>,
}

#[derive(Debug)]
pub struct TyAlias {
    pub owner_id: OwnerId,
    pub ty: Ty,
    pub span: Span,
    pub early_bound_params: Vec<RefineParam>,
    pub index_params: Vec<RefineParam>,
    /// Whether this alias was [lifted] from a `hir` alias
    ///
    /// [lifted]: lift::lift_type_alias
    pub lifted: bool,
}

#[derive(Debug)]
pub struct StructDef {
    pub owner_id: OwnerId,
    pub params: Vec<RefineParam>,
    pub kind: StructKind,
    pub invariants: Vec<Expr>,
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
    /// [lifted]: lift::lift_field_def
    pub lifted: bool,
}

#[derive(Debug)]
pub struct EnumDef {
    pub owner_id: OwnerId,
    pub params: Vec<RefineParam>,
    pub variants: Vec<VariantDef>,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct VariantDef {
    pub def_id: LocalDefId,
    pub params: Vec<RefineParam>,
    pub fields: Vec<Ty>,
    pub ret: VariantRet,
    pub span: Span,
    /// Whether this variant was [lifted] from a hir variant
    ///
    /// [lifted]: lift::lift_enum_variant_def
    pub lifted: bool,
}

#[derive(Debug)]
pub struct VariantRet {
    pub bty: BaseTy,
    pub idx: RefineArg,
}

pub struct FnSig {
    /// example: vec![(n: Int), (l: Loc)]
    pub params: Vec<RefineParam>,
    /// example: vec![(0 <= n), (l: i32)]
    pub requires: Vec<Constraint>,
    /// example: vec![(x: StrRef(l))]
    pub args: Vec<Ty>,
    pub output: FnOutput,
    /// Whether the sig was [lifted] from a hir signature
    ///
    /// [lifted]: lift::lift_fn_sig
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
    Type(Ident, Ty),
    /// A predicate that needs to hold
    Pred(Expr),
}

pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

pub enum TyKind {
    /// As a base type `bty` without any refinements is equivalent to `bty{vs : true}` we don't
    /// technically need this variant, but we keep it around to simplify desugaring.
    BaseTy(BaseTy),
    Indexed(BaseTy, RefineArg),
    Exists(Vec<RefineParam>, Box<Ty>),
    /// Constrained types `{T | p}` are like existentials but without binders, and are useful
    /// for specifying constraints on indexed values e.g. `{i32[@a] | 0 <= a}`
    Constr(Expr, Box<Ty>),
    Ptr(Ident),
    Ref(RefKind, Box<Ty>),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, ArrayLen),
    RawPtr(Box<Ty>, Mutability),
    Never,
}

pub struct ArrayLen {
    pub val: usize,
    pub span: Span,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Encodable, Decodable)]
pub enum RefKind {
    Shr,
    Mut,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum WeakKind {
    Shr,
    Mut,
    Arr,
}

pub struct WfckResults {
    owner: FluxOwnerId,
    node_sorts: ItemLocalMap<Sort>,
    coercions: ItemLocalMap<Vec<Coercion>>,
}

#[derive(Debug)]
pub enum Coercion {
    Inject,
    Project,
}

pub type ItemLocalMap<T> = FxHashMap<ItemLocalId, T>;

#[derive(Debug)]
pub struct LocalTableInContext<'a, T> {
    owner: FluxOwnerId,
    data: &'a ItemLocalMap<T>,
}

pub struct LocalTableInContextMut<'a, T> {
    owner: FluxOwnerId,
    data: &'a mut ItemLocalMap<T>,
}

impl From<BaseTy> for Ty {
    fn from(bty: BaseTy) -> Ty {
        let span = bty.span;
        Ty { kind: TyKind::BaseTy(bty), span }
    }
}

impl From<RefKind> for WeakKind {
    fn from(rk: RefKind) -> WeakKind {
        match rk {
            RefKind::Shr => WeakKind::Shr,
            RefKind::Mut => WeakKind::Mut,
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

pub enum RefineArg {
    Expr {
        expr: Expr,
        /// Whether this arg was used as a binder in the surface syntax. Used as a hint for
        /// inferring parameters at function calls.
        is_binder: bool,
    },
    Abs(Vec<RefineParam>, Expr, Span, FhirId),
    Record(DefId, Vec<RefineArg>, Span),
}

/// These are types of things that may be refined with indices or existentials
pub struct BaseTy {
    pub kind: BaseTyKind,
    pub span: Span,
}

pub enum BaseTyKind {
    Path(Path),
    Slice(Box<Ty>),
}

pub struct Path {
    pub res: Res,
    pub generics: Vec<Ty>,
    pub refine: Vec<RefineArg>,
    pub span: Span,
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum Res {
    PrimTy(PrimTy),
    Alias(DefId),
    Struct(DefId),
    Enum(DefId),
    Param(DefId),
}

#[derive(Debug, Clone)]
pub struct RefineParam {
    pub ident: Ident,
    pub sort: Sort,
    /// Inference mode for parameter at function calls. It has no meaning for parameters in other places.
    pub mode: InferMode,
    pub fhir_id: FhirId,
}

/// *Infer*ence *mode* for parameter at function calls
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum InferMode {
    /// Generate a fresh evar for the parameter and solve it via syntactic unification. The
    /// parameter must appear as an index for unification to succeed, but otherwise it can appear
    /// (mostly) freely.
    EVar,
    /// Generate a fresh kvar and let fixpoint infer it. This mode can only be used with abstract
    /// refinement predicates. If the parameter is marked as kvar then it can only appear in
    /// positions that result in a _horn_ constraint as required by fixpoint.
    KVar,
}

newtype_index! {
    /// A *Sort* *v*variable *id*
    #[debug_format = "#{}"]
    pub struct SortVid {}
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum Sort {
    Int,
    Bool,
    Real,
    Loc,
    Unit,
    BitVec(usize),
    Func(FuncSort),
    /// A record sort corresponds to the sort associated with a type alias or an adt (struct/enum).
    /// Values of a record sort can be projected using dot notation to extract their fields.
    Record(DefId),
    /// User defined opaque sort
    User(Symbol),
    /// The sort associated to a type variable
    Param(DefId),
    /// A sort that needs to be inferred
    Wildcard,
    /// Sort inference variable generated for a [Sort::Wildcard] during sort checking
    Infer(SortVid),
}

#[derive(Clone, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub struct FuncSort {
    pub inputs_and_output: List<Sort>,
}

pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub fhir_id: FhirId,
}

pub enum ExprKind {
    Const(DefId, Span),
    Var(Ident),
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

impl BaseTy {
    pub fn is_bool(&self) -> bool {
        matches!(self.kind, BaseTyKind::Path(Path { res: Res::PrimTy(PrimTy::Bool), .. }))
    }

    pub fn is_refined_by_record(&self) -> Option<DefId> {
        if let BaseTyKind::Path(path) = &self.kind
           && let Res::Struct(def_id) | Res::Enum(def_id) | Res::Alias(def_id) = path.res
        {
            Some(def_id)
        } else {
            None
        }
    }

    pub fn expect_param(&self) -> DefId {
        if let BaseTyKind::Path(path) = &self.kind
           && let Res::Param(def_id) = path.res
        {
            def_id
        } else {
            panic!("expected param")
        }
    }
}

impl Res {
    pub fn descr(&self) -> &'static str {
        match self {
            Res::PrimTy(_) => "builtin type",
            Res::Alias(_) => "type alias",
            Res::Struct(_) => "struct",
            Res::Enum(_) => "enum",
            Res::Param(_) => "type parameter",
        }
    }
}

impl From<Path> for BaseTy {
    fn from(path: Path) -> Self {
        let span = path.span;
        Self { kind: BaseTyKind::Path(path), span }
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
///
/// For a type alias `type A(x1: s1, x2: s2, ..)[y1: s, y2 : s, ..] = ..` we call `x1, x2, ..`
/// _early bound_ parameters. In contrast, `y1, y2, ..` are called _index parameters_. The term
/// [early bound] is borrowed from rust, but besides using the same name there's no connection
/// between both concepts. Our use is related to the positions a parameter is allowed to appear
/// in a definition.
///
/// [early bound]: https://rustc-dev-guide.rust-lang.org/early-late-bound.html
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct RefinedBy {
    pub def_id: DefId,
    pub span: Span,
    /// Index parameters indexed by their name and in the same order they appear in the definition.
    index_params: FxIndexMap<Symbol, Sort>,
    /// The number of early bound parameters
    early_bound: usize,
    /// Sorts of both early bound and index parameters. Early bound parameter appear first.
    sorts: Vec<Sort>,
}

#[derive(Debug)]
pub struct FuncDecl {
    pub name: Symbol,
    pub sort: FuncSort,
    pub kind: FuncKind,
}

#[derive(Debug, Clone, Copy, TyEncodable, TyDecodable, PartialEq, Eq, Hash)]
pub enum FuncKind {
    /// Theory symbols "interpreted" by the SMT solver
    Thy,
    /// User-defined uninterpreted functions with no definition
    Uif,
    /// User-defined functions with a body definition
    Def,
}

#[derive(Debug)]
pub struct Defn {
    pub name: Symbol,
    pub args: Vec<RefineParam>,
    pub sort: Sort,
    pub expr: Expr,
}

impl Generics {
    pub(crate) fn get_param(&self, def_id: LocalDefId) -> &GenericParamDef {
        self.params.iter().find(|p| p.def_id == def_id).unwrap()
    }
}

impl RefinedBy {
    pub fn new(
        def_id: impl Into<DefId>,
        early_bound_params: impl IntoIterator<Item = Sort>,
        index_params: impl IntoIterator<Item = (Symbol, Sort)>,
        span: Span,
    ) -> Self {
        let mut sorts = early_bound_params.into_iter().collect_vec();
        let early_bound = sorts.len();
        let index_params = index_params
            .into_iter()
            .inspect(|(_, sort)| sorts.push(sort.clone()))
            .collect();
        RefinedBy { def_id: def_id.into(), span, index_params, early_bound, sorts }
    }

    pub fn field_index(&self, fld: Symbol) -> Option<usize> {
        self.index_params.get_index_of(&fld)
    }

    pub fn field_sort(&self, fld: Symbol) -> Option<&Sort> {
        self.index_params.get(&fld)
    }

    pub fn early_bound_sorts(&self) -> &[Sort] {
        &self.sorts[..self.early_bound]
    }

    pub fn index_sorts(&self) -> &[Sort] {
        &self.sorts[self.early_bound..]
    }
}

impl Sort {
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

    /// Whether the sort is a function with return sort bool
    pub fn is_pred(&self) -> bool {
        matches!(self, Sort::Func(fsort) if fsort.output().is_bool())
    }

    pub fn default_infer_mode(&self) -> InferMode {
        if self.is_pred() {
            InferMode::KVar
        } else {
            InferMode::EVar
        }
    }
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

impl RefineParam {
    pub fn name(&self) -> Name {
        self.ident.name
    }
}

impl From<FuncSort> for Sort {
    fn from(sort: FuncSort) -> Self {
        Self::Func(sort)
    }
}

impl FuncSort {
    pub fn new(mut inputs: Vec<Sort>, output: Sort) -> Self {
        inputs.push(output);
        FuncSort { inputs_and_output: List::from_vec(inputs) }
    }

    pub fn inputs(&self) -> &[Sort] {
        &self.inputs_and_output[..self.inputs_and_output.len() - 1]
    }

    pub fn output(&self) -> &Sort {
        &self.inputs_and_output[self.inputs_and_output.len() - 1]
    }
}

impl rustc_errors::IntoDiagnosticArg for Sort {
    fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
        rustc_errors::DiagnosticArgValue::Str(Cow::Owned(format!("{self}")))
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

impl Map {
    pub fn new() -> Self {
        let mut me = Self::default();
        me.insert_theory_funcs();
        me
    }

    pub fn insert_generics(&mut self, def_id: LocalDefId, generics: Generics) {
        self.generics.insert(def_id, generics);
    }

    pub fn get_generics(&self, def_id: LocalDefId) -> Option<&Generics> {
        self.generics.get(&def_id)
    }

    pub fn generics(&self) -> impl Iterator<Item = (&LocalDefId, &Generics)> {
        self.generics.iter()
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

    pub fn fn_sigs(&self) -> impl Iterator<Item = (LocalDefId, &FnSig)> {
        self.fns.iter().map(|(def_id, fn_sig)| (*def_id, fn_sig))
    }

    pub fn get_fn_sig(&self, def_id: LocalDefId) -> &FnSig {
        &self.fns[&def_id]
    }

    pub fn fn_quals(&self) -> impl Iterator<Item = (LocalDefId, &Vec<SurfaceIdent>)> {
        self.fn_quals.iter().map(|(def_id, quals)| (*def_id, quals))
    }

    pub fn is_trusted(&self, def_id: LocalDefId) -> bool {
        self.trusted.contains(&def_id)
    }

    pub fn insert_extern(&mut self, extern_def_id: DefId, local_def_id: LocalDefId) {
        self.externs.insert(extern_def_id, local_def_id);
    }

    pub fn externs(&self) -> &FxHashMap<DefId, LocalDefId> {
        &self.externs
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

    pub fn type_aliases(&self) -> impl Iterator<Item = &TyAlias> {
        self.type_aliases.values()
    }

    pub fn get_type_alias(&self, def_id: impl Borrow<LocalDefId>) -> &TyAlias {
        &self.type_aliases[def_id.borrow()]
    }

    // Structs

    pub fn insert_struct(&mut self, def_id: LocalDefId, struct_def: StructDef) {
        self.structs.insert(def_id, struct_def);
    }

    pub fn structs(&self) -> impl Iterator<Item = &StructDef> {
        self.structs.values()
    }

    pub fn get_struct(&self, def_id: impl Borrow<LocalDefId>) -> &StructDef {
        &self.structs[def_id.borrow()]
    }

    // Enums

    pub fn insert_enum(&mut self, def_id: LocalDefId, enum_def: EnumDef) {
        self.enums.insert(def_id, enum_def);
    }

    pub fn enums(&self) -> impl Iterator<Item = &EnumDef> {
        self.enums.values()
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
    fn insert_theory_func(&mut self, name: Symbol, inputs: Vec<Sort>, output: Sort) {
        let sort = FuncSort::new(inputs, output);
        self.func_decls
            .insert(name, FuncDecl { name, sort, kind: FuncKind::Thy });
    }

    fn insert_theory_funcs(&mut self) {
        self.insert_theory_func(Symbol::intern("int_to_bv32"), vec![Sort::Int], Sort::BitVec(32));
        self.insert_theory_func(Symbol::intern("bv32_to_int"), vec![Sort::BitVec(32)], Sort::Int);
        self.insert_theory_func(
            Symbol::intern("bvsub"),
            vec![Sort::BitVec(32), Sort::BitVec(32)],
            Sort::BitVec(32),
        );
        self.insert_theory_func(
            Symbol::intern("bvand"),
            vec![Sort::BitVec(32), Sort::BitVec(32)],
            Sort::BitVec(32),
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

    pub fn sort_decl(&self, name: impl Borrow<Symbol>) -> Option<&SortDecl> {
        self.sort_decls.get(name.borrow())
    }

    pub fn get_flux_item(&self, name: impl Borrow<Symbol>) -> Option<&FluxItem> {
        self.flux_items.get(name.borrow())
    }
}

impl TyAlias {
    pub fn all_params(&self) -> impl Iterator<Item = &RefineParam> {
        self.early_bound_params.iter().chain(&self.index_params)
    }
}

impl StructDef {
    pub fn is_opaque(&self) -> bool {
        matches!(self.kind, StructKind::Opaque)
    }
}

impl WfckResults {
    pub fn new(owner: FluxOwnerId) -> Self {
        Self { owner, node_sorts: ItemLocalMap::default(), coercions: ItemLocalMap::default() }
    }

    pub fn node_sorts_mut(&mut self) -> LocalTableInContextMut<Sort> {
        LocalTableInContextMut { owner: self.owner, data: &mut self.node_sorts }
    }

    pub fn node_sorts(&self) -> LocalTableInContext<Sort> {
        LocalTableInContext { owner: self.owner, data: &self.node_sorts }
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

impl_internable!([Sort]);

impl fmt::Debug for FnSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.params.is_empty() {
            write!(
                f,
                "for<{}> ",
                self.params.iter().format_with(", ", |param, f| {
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
            Constraint::Type(loc, ty) => write!(f, "{loc:?}: {ty:?}"),
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
            TyKind::Ptr(loc) => write!(f, "ref<{loc:?}>"),
            TyKind::Ref(RefKind::Mut, ty) => write!(f, "&mut {ty:?}"),
            TyKind::Ref(RefKind::Shr, ty) => write!(f, "&{ty:?}"),
            TyKind::Tuple(tys) => write!(f, "({:?})", tys.iter().format(", ")),
            TyKind::Array(ty, len) => write!(f, "[{ty:?}; {len:?}]"),
            TyKind::Never => write!(f, "!"),
            TyKind::Constr(pred, ty) => write!(f, "{{{ty:?} | {pred:?}}}"),
            TyKind::RawPtr(ty, Mutability::Not) => write!(f, "*const {ty:?}"),
            TyKind::RawPtr(ty, Mutability::Mut) => write!(f, "*mut {ty:?}"),
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
            BaseTyKind::Path(path) => write!(f, "{path:?}"),
            BaseTyKind::Slice(ty) => write!(f, "[{ty:?}]"),
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
            Res::Alias(def_id) | Res::Struct(def_id) | Res::Enum(def_id) | Res::Param(def_id) => {
                write!(f, "{}", pretty::def_id_to_string(def_id))?;
            }
        }
        if !self.generics.is_empty() {
            write!(f, "<{:?}>", self.generics.iter().format(", "))?;
        }
        if !self.refine.is_empty() {
            write!(f, "({:?})", self.refine.iter().format(", "))?;
        }
        Ok(())
    }
}

impl fmt::Debug for RefineArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefineArg::Expr { expr, is_binder, .. } => {
                if *is_binder {
                    write!(f, "@")?;
                }
                write!(f, "{expr:?}")
            }
            RefineArg::Abs(params, body, ..) => {
                write!(
                    f,
                    "|{}| {body:?}",
                    params.iter().format_with(", ", |param, f| {
                        f(&format_args!("{:?}: {:?}", param.ident, param.sort))
                    })
                )
            }
            RefineArg::Record(def_id, flds, ..) => {
                write!(
                    f,
                    "{} {{ {:?} }}",
                    pretty::def_id_to_string(*def_id),
                    flds.iter().format(", ")
                )
            }
        }
    }
}

impl fmt::Debug for RefKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefKind::Shr => write!(f, "shr"),
            RefKind::Mut => write!(f, "mut"),
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

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Sort::Infer(_) = self {
            write!(f, "_")
        } else {
            fmt::Debug::fmt(self, f)
        }
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "bool"),
            Sort::Int => write!(f, "int"),
            Sort::Real => write!(f, "real"),
            Sort::BitVec(w) => write!(f, "bitvec({w})"),
            Sort::Loc => write!(f, "loc"),
            Sort::Func(sort) => write!(f, "{sort}"),
            Sort::Unit => write!(f, "()"),
            Sort::Record(def_id) => write!(f, "{}", pretty::def_id_to_string(*def_id)),
            Sort::User(name) => write!(f, "{name}"),
            Sort::Param(def_id) => write!(f, "sortof({})", pretty::def_id_to_string(*def_id)),
            Sort::Wildcard => write!(f, "_"),
            Sort::Infer(vid) => write!(f, "{vid:?}"),
        }
    }
}

impl fmt::Display for FuncSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.inputs() {
            [input] => {
                write!(f, "{} -> {}", input, self.output())
            }
            inputs => {
                write!(f, "({}) -> {}", inputs.iter().join(", "), self.output())
            }
        }
    }
}

impl fmt::Debug for FuncSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
