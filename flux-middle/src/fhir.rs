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

use std::{
    borrow::{Borrow, Cow},
    fmt,
    fmt::Write,
};

use flux_common::format::PadAdapter;
pub use flux_fixpoint::{BinOp, UnOp};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::newtype_index;
pub use rustc_middle::ty::{FloatTy, IntTy, ParamTy, UintTy};
use rustc_span::{Span, Symbol, DUMMY_SP};
pub use rustc_target::abi::VariantIdx;

use crate::{
    intern::{impl_internable, List},
    pretty,
};

#[derive(Debug, Clone)]
pub struct ConstInfo {
    pub def_id: DefId,
    pub sym: Symbol,
    pub val: i128,
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: String,
    pub args: Vec<(Ident, Sort)>,
    pub expr: Expr,
}

/// A map between rust definitions and flux annotations in their desugared `fhir` form.
///
/// note: `Map` is a very generic name, so we typically use the type qualified as `fhir::Map`.
#[derive(Default, Debug)]
pub struct Map {
    uifs: FxHashMap<Symbol, UifDef>,
    defns: FxHashMap<Symbol, Defn>,
    consts: FxHashMap<Symbol, ConstInfo>,
    qualifiers: Vec<Qualifier>,
    adts: FxHashMap<LocalDefId, AdtDef>,
    structs: FxHashMap<LocalDefId, StructDef>,
    enums: FxHashMap<LocalDefId, EnumDef>,
    fns: FxHashMap<LocalDefId, FnSig>,
    trusted: FxHashSet<LocalDefId>,
}

#[derive(Debug)]
pub struct StructDef {
    pub def_id: DefId,
    pub kind: StructKind,
}

#[derive(Debug)]
pub enum StructKind {
    Transparent { fields: Vec<Option<Ty>> },
    Opaque,
}

#[derive(Debug)]
pub struct EnumDef {
    pub def_id: DefId,
    pub variants: Vec<VariantDef>,
}

#[derive(Debug)]
pub struct VariantDef {
    pub params: Vec<RefineParam>,
    pub fields: Vec<Ty>,
    pub ret: VariantRet,
}

#[derive(Debug)]
pub struct VariantRet {
    pub bty: BaseTy,
    pub idx: Index,
}

pub struct FnSig {
    /// example: vec![(n: Int), (l: Loc)]
    pub params: Vec<RefineParam>,
    /// example: vec![(0 <= n), (l: i32)]
    pub requires: Vec<Constraint>,
    /// example: vec![(x: StrRef(l))]
    pub args: Vec<Ty>,
    /// example: i32
    pub ret: Ty,
    /// example: vec![(l: i32{v:n < v})]
    pub ensures: Vec<Constraint>,
}

pub enum Constraint {
    /// A type constraint on a location
    Type(Ident, Ty),
    /// A predicate that needs to hold
    Pred(Expr),
}

pub enum Ty {
    /// As a base type `bty` without any refinements is equivalent to `bty{vs : true}` we don't
    /// technically need this variant, but we keep it around to simplify desugaring.
    BaseTy(BaseTy),
    Indexed(BaseTy, Index),
    Exists(BaseTy, Ident, Expr),
    /// Constrained types `{T : p}` are like existentials but without binders, and are useful
    /// for specifying constraints on indexed values e.g. `{i32[@a] | 0 <= a}`
    Constr(Expr, Box<Ty>),
    Float(FloatTy),
    Str,
    Char,
    Ptr(Ident),
    Ref(RefKind, Box<Ty>),
    Param(ParamTy),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, ArrayLen),
    Never,
}

pub struct ArrayLen {
    pub val: usize,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
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

impl From<RefKind> for WeakKind {
    fn from(rk: RefKind) -> WeakKind {
        match rk {
            RefKind::Shr => WeakKind::Shr,
            RefKind::Mut => WeakKind::Mut,
        }
    }
}

pub struct Index {
    pub kind: IndexKind,
    pub span: Span,
}

pub enum IndexKind {
    Single(RefineArg),
    Aggregate(DefId, Vec<RefineArg>),
}

pub enum RefineArg {
    Expr {
        expr: Expr,
        /// Whether this arg was used as a binder in the surface syntax. Used as a hint for
        /// inferring parameters at function calls.
        is_binder: bool,
    },
    Abs(Vec<Name>, Expr, Span),
}

/// These are types of things that may be refined with indices or existentials
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(DefId, Vec<Ty>),
    Slice(Box<Ty>),
}

#[derive(Debug)]
pub struct RefineParam {
    pub name: Ident,
    pub sort: Sort,
    pub mode: InferMode,
}

/// *Infer*ence *mode* for parameter at function calls
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferMode {
    /// Generate a fresh evar for the parameter and solve it via syntactic unification. The
    /// parameter must appear as an index for unification to succeed, but otherwise it can appear
    /// (mostly) freely.
    EVar,
    /// Generate a fresh kvar and let fixpoint infer it. This mode can only be used with abstract
    /// refinements predicates. If the parameter is marked as kvar then it can only appear in
    /// positions that result in a _horn_ constraint as required by fixpoint.
    KVar,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    Int,
    Bool,
    Loc,
    Tuple(List<Sort>),
    Func(FuncSort),
    Adt(DefId),
    Infer,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct FuncSort {
    pub inputs_and_output: List<Sort>,
}

pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

pub enum ExprKind {
    Const(DefId, Span),
    Var(Ident),
    Dot(Ident, Symbol, Span),
    Literal(Lit),
    BinaryOp(BinOp, Box<[Expr; 2]>),
    UnaryOp(UnOp, Box<Expr>),
    App(Func, Vec<Expr>),
    IfThenElse(Box<[Expr; 3]>),
}

#[derive(Clone)]
pub enum Func {
    /// A function comming from a refinement parameter.
    Var(Ident),
    /// A _global_ uninterpreted function.
    Uif(Symbol, Span),
}

/// representation of uninterpreted functions
pub struct UFun {
    pub symbol: Symbol,
    pub span: Span,
}

#[derive(Clone, Copy)]
pub enum Lit {
    Int(i128),
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

impl BaseTy {
    /// Returns `true` if the base ty is [`Bool`].
    ///
    /// [`Bool`]: BaseTy::Bool
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    pub fn sort(&self) -> Sort {
        match self {
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Slice(_) => Sort::Int,
            BaseTy::Bool => Sort::Bool,
            BaseTy::Adt(def_id, _) => Sort::Adt(*def_id),
        }
    }
}

impl Index {
    pub fn flatten(&self) -> &[RefineArg] {
        match &self.kind {
            IndexKind::Single(arg) => std::slice::from_ref(arg),
            IndexKind::Aggregate(_, args) => args,
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

#[derive(Debug)]
pub struct AdtDef {
    pub def_id: DefId,
    pub refined_by: RefinedBy,
    pub invariants: Vec<Expr>,
    pub opaque: bool,
    sorts: Vec<Sort>,
}

#[derive(Debug)]
pub struct RefinedBy {
    pub params: Vec<(Ident, Sort)>,
    pub span: Span,
}

#[derive(Debug)]
pub struct UifDef {
    pub name: Symbol,
    pub sort: FuncSort,
}

#[derive(Debug)]
pub struct Defn {
    pub name: Symbol,
    pub args: Vec<(Ident, Sort)>,
    pub sort: Sort,
    pub expr: Expr,
}

impl AdtDef {
    pub fn new(def_id: DefId, refined_by: RefinedBy, invariants: Vec<Expr>, opaque: bool) -> Self {
        let sorts = refined_by.sorts().cloned().collect_vec();
        AdtDef { def_id, refined_by, invariants, opaque, sorts }
    }

    pub fn field_index(&self, fld: Symbol) -> Option<usize> {
        self.refined_by
            .params
            .iter()
            .find_position(|(ident, _)| ident.sym() == fld)
            .map(|res| res.0)
    }

    pub fn field_sort(&self, fld: Symbol) -> Option<&Sort> {
        self.refined_by.params.iter().find_map(
            |(ident, sort)| {
                if ident.sym() == fld {
                    Some(sort)
                } else {
                    None
                }
            },
        )
    }
}

impl RefinedBy {
    pub const DUMMY: &'static RefinedBy = &RefinedBy { params: vec![], span: DUMMY_SP };

    pub fn sorts(&self) -> impl Iterator<Item = &Sort> {
        self.params.iter().map(|(_, sort)| sort)
    }
}

impl Sort {
    pub fn tuple(sorts: impl Into<List<Sort>>) -> Self {
        Sort::Tuple(sorts.into())
    }

    pub fn unit() -> Self {
        Self::tuple(vec![])
    }

    /// Returns `true` if the sort is [`Bool`].
    ///
    /// [`Bool`]: Sort::Bool
    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    /// Returns `true` if the sort is [`Loc`].
    ///
    /// [`Loc`]: Sort::Loc
    #[must_use]
    pub fn is_loc(&self) -> bool {
        matches!(self, Self::Loc)
    }

    /// Whether the sort is a function with return sort bool
    pub fn is_pred(&self) -> bool {
        matches!(self, Sort::Func(fsort) if fsort.output().is_bool())
    }

    #[track_caller]
    pub fn as_func(&self) -> &FuncSort {
        if let Sort::Func(sort) = self {
            sort
        } else {
            panic!("expected `Sort::Func`")
        }
    }

    pub fn default_infer_mode(&self) -> InferMode {
        if self.is_pred() {
            InferMode::KVar
        } else {
            InferMode::EVar
        }
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
        rustc_errors::DiagnosticArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

impl Map {
    // Qualifiers

    pub fn insert_qualifier(&mut self, qualifier: Qualifier) {
        self.qualifiers.push(qualifier);
    }

    pub fn qualifiers(&self) -> impl Iterator<Item = &Qualifier> {
        self.qualifiers.iter()
    }

    // FnSigs

    pub fn insert_fn_sig(&mut self, def_id: LocalDefId, fn_sig: FnSig) {
        self.fns.insert(def_id, fn_sig);
    }

    pub fn add_trusted(&mut self, def_id: LocalDefId) {
        self.trusted.insert(def_id);
    }

    pub fn fn_sigs(&self) -> impl Iterator<Item = (LocalDefId, &FnSig)> {
        self.fns.iter().map(|(def_id, fn_sig)| (*def_id, fn_sig))
    }

    pub fn is_trusted(&self, def_id: DefId) -> bool {
        if let Some(def_id) = def_id.as_local() {
            self.trusted.contains(&def_id)
        } else {
            false
        }
    }

    // Structs

    pub fn insert_struct(&mut self, def_id: LocalDefId, struct_def: StructDef) {
        self.structs.insert(def_id, struct_def);
    }

    pub fn structs(&self) -> impl Iterator<Item = &StructDef> {
        self.structs.values()
    }

    // Enums

    pub fn insert_enum(&mut self, def_id: LocalDefId, enum_def: EnumDef) {
        self.enums.insert(def_id, enum_def);
    }

    pub fn enums(&self) -> impl Iterator<Item = &EnumDef> {
        self.enums.values()
    }

    // Consts

    pub fn insert_const(&mut self, c: ConstInfo) {
        self.consts.insert(c.sym, c);
    }

    pub fn consts(&self) -> impl Iterator<Item = &ConstInfo> {
        self.consts.values()
    }

    pub fn const_by_name(&self, name: Symbol) -> Option<&ConstInfo> {
        self.consts.get(&name)
    }

    // UIF

    pub fn insert_uif(&mut self, symb: Symbol, uif: UifDef) {
        self.uifs.insert(symb, uif);
    }

    pub fn uifs(&self) -> impl Iterator<Item = &UifDef> {
        self.uifs.values()
    }

    pub fn uif(&self, sym: impl Borrow<Symbol>) -> Option<&UifDef> {
        self.uifs.get(sym.borrow())
    }

    // Defn
    pub fn insert_defn(&mut self, symb: Symbol, defn: Defn) {
        self.defns.insert(symb, defn);
    }

    pub fn defns(&self) -> impl Iterator<Item = &Defn> {
        self.defns.values()
    }

    pub fn defn(&self, sym: impl Borrow<Symbol>) -> Option<&Defn> {
        self.defns.get(sym.borrow())
    }

    // ADT

    pub fn insert_adt(&mut self, def_id: LocalDefId, sort_info: AdtDef) {
        self.adts.insert(def_id, sort_info);
    }

    pub fn sorts_of(&self, def_id: DefId) -> Option<&[Sort]> {
        let info = self.adts.get(&def_id.as_local()?)?;
        Some(&info.sorts)
    }

    pub fn refined_by(&self, def_id: DefId) -> Option<&RefinedBy> {
        let adt_def = self.adts.get(&def_id.as_local()?)?;
        Some(&adt_def.refined_by)
    }

    pub fn adt(&self, def_id: LocalDefId) -> &AdtDef {
        &self.adts[&def_id]
    }

    pub fn adts(&self) -> impl Iterator<Item = &AdtDef> {
        self.adts.values()
    }
}

impl_internable!([Sort]);

impl fmt::Debug for FnSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            let mut p = PadAdapter::wrap_fmt(f, 4);
            write!(p, "(\nfn")?;
            if !self.params.is_empty() {
                write!(
                    p,
                    "<{}>",
                    self.params.iter().format_with(", ", |param, f| {
                        match param.mode {
                            InferMode::KVar => {
                                f(&format_args!("${:?}: {:?}", param.name, param.sort))
                            }
                            InferMode::EVar => {
                                f(&format_args!("?{:?}: {:?}", param.name, param.sort))
                            }
                        }
                    })
                )?;
            }
            write!(p, "({:?}) -> {:?}", self.args.iter().format(", "), self.ret)?;
            if !self.requires.is_empty() {
                write!(p, "\nrequires {:?} ", self.requires.iter().format(", "))?;
            }
            if !self.ensures.is_empty() {
                write!(p, "\nensures {:?}", self.ensures.iter().format(", "))?;
            }
            write!(f, "\n)")?;
        } else {
            if !self.params.is_empty() {
                write!(
                    f,
                    "for<{}> ",
                    self.params.iter().format_with(", ", |param, f| {
                        f(&format_args!("{:?}: {:?}", param.name, param.sort))
                    })
                )?;
            }
            if !self.requires.is_empty() {
                write!(f, "[{:?}] ", self.requires.iter().format(", "))?;
            }
            write!(f, "fn({:?}) -> {:?}", self.args.iter().format(", "), self.ret)?;
            if !self.ensures.is_empty() {
                write!(f, "; [{:?}]", self.ensures.iter().format(", "))?;
            }
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
        match self {
            Ty::BaseTy(bty) => write!(f, "{bty:?}{{}}"),
            Ty::Indexed(bty, idx) => write!(f, "{bty:?}{idx:?}"),
            Ty::Exists(bty, bind, p) => write!(f, "{bty:?}{{{bind:?} : {p:?}}}"),
            Ty::Float(float_ty) => write!(f, "{}", float_ty.name_str()),
            Ty::Ptr(loc) => write!(f, "ref<{loc:?}>"),
            Ty::Ref(RefKind::Mut, ty) => write!(f, "&mut {ty:?}"),
            Ty::Ref(RefKind::Shr, ty) => write!(f, "&{ty:?}"),
            Ty::Param(param) => write!(f, "{param}"),
            Ty::Tuple(tys) => write!(f, "({:?})", tys.iter().format(", ")),
            Ty::Array(ty, len) => write!(f, "[{ty:?}; {len:?}]"),
            Ty::Never => write!(f, "!"),
            Ty::Constr(pred, ty) => write!(f, "{{{ty:?} : {pred:?}}}"),
            Ty::Str => write!(f, "str"),
            Ty::Char => write!(f, "char"),
        }
    }
}

impl fmt::Debug for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            IndexKind::Single(idx) => {
                write!(f, "{idx:?}")
            }
            IndexKind::Aggregate(def_id, flds) => {
                write!(
                    f,
                    "[{}{{ {:?} }}]",
                    pretty::def_id_to_string(*def_id),
                    flds.iter().format(", ")
                )
            }
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
        match self {
            BaseTy::Int(int_ty) => write!(f, "{}", int_ty.name_str())?,
            BaseTy::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str())?,
            BaseTy::Bool => write!(f, "bool")?,
            BaseTy::Adt(did, _) => write!(f, "{}", pretty::def_id_to_string(*did))?,
            BaseTy::Slice(ty) => write!(f, "[{ty:?}]")?,
        }
        if let BaseTy::Adt(_, substs) = self && !substs.is_empty() {
            write!(f, "<{:?}>", substs.iter().format(", "))?;
        }
        Ok(())
    }
}

impl fmt::Debug for RefineArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RefineArg::Expr { expr, is_binder } => {
                if *is_binder {
                    write!(f, "@")?;
                }
                write!(f, "{expr:?}")
            }
            RefineArg::Abs(params, body, _) => {
                write!(f, "|{:?}| {body:?}", params.iter().format(","))
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
impl fmt::Debug for UFun {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sym = self.symbol;
        write!(f, "{sym:?}")
    }
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ExprKind::Var(x, ..) => write!(f, "{x:?}"),
            ExprKind::BinaryOp(op, box [e1, e2]) => write!(f, "({e1:?} {op:?} {e2:?})"),
            ExprKind::UnaryOp(op, e) => write!(f, "{op:?}{e:?}"),
            ExprKind::Literal(lit) => write!(f, "{lit:?}"),
            ExprKind::Const(x, _) => write!(f, "{x:?}"),
            ExprKind::App(uf, es) => write!(f, "{uf:?}({es:?})"),
            ExprKind::IfThenElse(box [p, e1, e2]) => {
                write!(f, "(if {p:?} {{ {e1:?} }} else {{ {e2:?} }})")
            }
            ExprKind::Dot(var, fld, _) => write!(f, "{var:?}.{fld}"),
        }
    }
}

impl fmt::Debug for Func {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(func) => write!(f, "{func:?}"),
            Self::Uif(sym, _) => write!(f, "{sym}"),
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
            Lit::Bool(b) => write!(f, "{b}"),
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "bool"),
            Sort::Int => write!(f, "int"),
            Sort::Loc => write!(f, "loc"),
            Sort::Func(sort) => write!(f, "{sort}"),
            Sort::Tuple(sorts) => write!(f, "({})", sorts.iter().join(", ")),
            Sort::Adt(def_id) => write!(f, "{}", pretty::def_id_to_string(*def_id)),
            Sort::Infer => write!(f, "_"),
        }
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for FuncSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}) -> {}", self.inputs().iter().join(","), self.output())
    }
}

impl fmt::Debug for FuncSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl rustc_errors::IntoDiagnosticArg for &Sort {
    fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
        let cow = match self {
            Sort::Bool => Cow::Borrowed("bool"),
            Sort::Int => Cow::Borrowed("int"),
            Sort::Loc => Cow::Borrowed("loc"),
            _ => Cow::Owned(format!("{self}")),
        };
        rustc_errors::DiagnosticArgValue::Str(cow)
    }
}

impl rustc_errors::IntoDiagnosticArg for &FuncSort {
    fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
        rustc_errors::DiagnosticArgValue::Str(Cow::Owned(format!("{self}")))
    }
}
