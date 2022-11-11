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

use std::{borrow::Cow, fmt, fmt::Write};

use flux_common::format::PadAdapter;
pub use flux_fixpoint::BinOp;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::newtype_index;
pub use rustc_middle::ty::{FloatTy, IntTy, ParamTy, UintTy};
use rustc_span::{Span, Symbol, DUMMY_SP};
pub use rustc_target::abi::VariantIdx;

use crate::pretty;

#[derive(Debug, Clone)]
pub struct ConstInfo {
    pub def_id: DefId,
    pub sym: Symbol,
    pub val: i128,
}

/// A map between rust definitions and flux annotations in their desugared `fhir` form.
///
/// note: `Map` is a very generic name, so we typically qualify the type as `fhir::Map` when
/// using it.
#[derive(Default, Debug)]
pub struct Map {
    uifs: FxHashMap<Symbol, UifDef>,
    consts: FxHashMap<Symbol, ConstInfo>,
    qualifiers: Vec<Qualifier>,
    adts: FxHashMap<LocalDefId, AdtDef>,
    structs: FxHashMap<LocalDefId, StructDef>,
    enums: FxHashMap<LocalDefId, EnumDef>,
    fns: FxHashMap<LocalDefId, FnSig>,
    assumes: FxHashSet<LocalDefId>,
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
    pub refined_by: Vec<Param>,
    pub variants: Vec<VariantDef>,
}

#[derive(Debug)]
pub struct VariantDef {
    pub params: Vec<Param>,
    pub fields: Vec<Ty>,
    pub ret: VariantRet,
}

#[derive(Debug)]
pub struct VariantRet {
    pub bty: BaseTy,
    pub indices: Indices,
}

pub struct FnSig {
    /// example: vec![(n: Int), (l: Loc)]
    pub params: Vec<Param>,
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

#[derive(Debug)]
pub struct Qualifier {
    pub name: String,
    pub args: Vec<Param>,
    pub expr: Expr,
}

pub struct ConstSig {
    pub def_id: DefId,
    pub val: i128,
    pub ty: Ty,
}

pub enum Ty {
    /// As a base type `bty` without any refinements is equivalent to `bty{vs : true}` we don't
    /// technically need this variant, but we keep it around to simplify desugaring.
    BaseTy(BaseTy),
    Indexed(BaseTy, Indices),
    /// Existential types in fhir are represented with an explicit list of binders for
    /// every index of the [`BaseTy`], e.g., `i32{v : v > 0}` for one index and `RMat{v0,v1 : v0 == v1}`.
    /// for two indices. There's currently no equivalent surface syntax and existentials for
    /// types with multiple indices have to use projection syntax.
    Exists(BaseTy, Vec<Name>, Expr),
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
    Slice(Box<Ty>),
    Never,
}

pub struct ArrayLen;

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

pub struct Indices {
    pub indices: Vec<Index>,
    pub span: Span,
}

pub struct Index {
    pub expr: Expr,
    /// Whether this index was used as a binder in the surface syntax. Used as a hint for inferring
    /// parameters at function calls.
    pub is_binder: bool,
}

pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(DefId, Vec<Ty>),
}

#[derive(Debug, Clone, Copy)]
pub struct Param {
    pub name: Ident,
    pub sort: Sort,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Sort {
    Bool,
    Int,
    Loc,
}

pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

pub enum ExprKind {
    Const(DefId, Span),
    Var(Name, Symbol, Span),
    Literal(Lit),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
    App(UFun, Vec<Expr>),
    IfThenElse(Box<Expr>, Box<Expr>, Box<Expr>),
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

#[derive(Clone, Copy)]
pub struct Ident {
    pub name: Name,
    pub source_info: (Span, Symbol),
}

newtype_index! {
    pub struct Name {
        DEBUG_FORMAT = "x{}",
    }
}

impl BaseTy {
    /// Returns `true` if the base ty is [`Bool`].
    ///
    /// [`Bool`]: BaseTy::Bool
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }
}

impl<'a> IntoIterator for &'a Indices {
    type Item = &'a Index;

    type IntoIter = std::slice::Iter<'a, Index>;

    fn into_iter(self) -> Self::IntoIter {
        self.indices.iter()
    }
}

impl Lit {
    pub const TRUE: Lit = Lit::Bool(true);
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
    pub params: Vec<Param>,
    pub span: Span,
}

#[derive(Debug)]
pub struct UifDef {
    pub inputs: Vec<Sort>,
    pub output: Sort,
}

impl AdtDef {
    pub fn new(def_id: DefId, refined_by: RefinedBy, invariants: Vec<Expr>, opaque: bool) -> Self {
        let sorts = refined_by.iter().map(|param| param.sort).collect();
        AdtDef { def_id, refined_by, invariants, opaque, sorts }
    }
}

impl RefinedBy {
    pub const DUMMY: &'static RefinedBy = &RefinedBy { params: vec![], span: DUMMY_SP };
    pub fn iter(&self) -> impl Iterator<Item = &Param> {
        self.params.iter()
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

    pub fn add_assumed(&mut self, def_id: LocalDefId) {
        self.assumes.insert(def_id);
    }

    pub fn fn_sigs(&self) -> impl Iterator<Item = (DefId, &FnSig)> {
        self.fns
            .iter()
            .map(|(def_id, fn_sig)| (def_id.to_def_id(), fn_sig))
    }

    pub fn assumed(&self, def_id: DefId) -> bool {
        if let Some(def_id) = def_id.as_local() {
            self.assumes.contains(&def_id)
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

    pub fn uifs(&self) -> impl Iterator<Item = (&Symbol, &UifDef)> {
        self.uifs.iter()
    }

    pub fn uif(&self, sym: Symbol) -> Option<&UifDef> {
        self.uifs.get(&sym)
    }

    // ADT

    pub fn insert_adt(&mut self, def_id: LocalDefId, sort_info: AdtDef) {
        self.adts.insert(def_id, sort_info);
    }

    pub fn sorts(&self, def_id: DefId) -> Option<&[Sort]> {
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
                        f(&format_args!("{:?}: {:?}", param.name, param.sort))
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
            Ty::Indexed(bty, idxs) => {
                write!(f, "{bty:?}")?;
                if !idxs.indices.is_empty() {
                    write!(f, "[{:?}]", idxs.indices.iter().format(", "))?;
                }
                Ok(())
            }
            Ty::Exists(bty, binders, p) => {
                write!(f, "{bty:?}{{{binders:?} : {p:?}}}")
            }
            Ty::Float(float_ty) => write!(f, "{}", float_ty.name_str()),
            Ty::Ptr(loc) => write!(f, "ref<{loc:?}>"),
            Ty::Ref(RefKind::Mut, ty) => write!(f, "&mut {ty:?}"),
            Ty::Ref(RefKind::Shr, ty) => write!(f, "&{ty:?}"),
            Ty::Param(param) => write!(f, "{param}"),
            Ty::Tuple(tys) => write!(f, "({:?})", tys.iter().format(", ")),
            Ty::Never => write!(f, "!"),
            Ty::Constr(pred, ty) => write!(f, "{{{ty:?} : {pred:?}}}"),
            Ty::Array(ty, len) => write!(f, "[{ty:?}; {len:?}]"),
            Ty::Slice(ty) => write!(f, "[{ty:?}]"),
            Ty::Str => write!(f, "str"),
            Ty::Char => write!(f, "char"),
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
        }
        if let BaseTy::Adt(_, substs) = self && !substs.is_empty() {
            write!(f, "<{:?}>", substs.iter().format(", "))?;
        }
        Ok(())
    }
}

impl fmt::Debug for Indices {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{:?}]", self.indices.iter().format(", "))
    }
}

impl fmt::Debug for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_binder {
            write!(f, "@")?;
        }
        write!(f, "{:?}", self.expr)
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
            ExprKind::BinaryOp(op, e1, e2) => write!(f, "({e1:?} {op:?} {e2:?})"),
            ExprKind::Literal(lit) => write!(f, "{lit:?}"),
            ExprKind::Const(x, _) => write!(f, "{x:?}"),
            ExprKind::App(uf, es) => write!(f, "{uf:?}({es:?})"),
            ExprKind::IfThenElse(p, e1, e2) => {
                write!(f, "(if {p:?} {{ {e1:?} }} else {{ {e2:?} }})")
            }
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

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "bool"),
            Sort::Int => write!(f, "int"),
            Sort::Loc => write!(f, "loc"),
        }
    }
}

impl rustc_errors::IntoDiagnosticArg for Sort {
    fn into_diagnostic_arg(self) -> rustc_errors::DiagnosticArgValue<'static> {
        let cow = match self {
            Sort::Bool => Cow::Borrowed("bool"),
            Sort::Int => Cow::Borrowed("int"),
            Sort::Loc => Cow::Borrowed("loc"),
        };
        rustc_errors::DiagnosticArgValue::Str(cow)
    }
}
