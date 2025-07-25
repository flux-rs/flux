pub mod visit;

use std::{borrow::Cow, fmt, ops::Range};

pub use rustc_ast::{
    Mutability,
    token::{Lit, LitKind},
};
pub use rustc_span::{Span, symbol::Ident};
use rustc_span::{Symbol, symbol::sym};

use crate::surface::visit::Visitor;

/// A [`NodeId`] is a unique identifier we assign to some AST nodes to be able to attach information
/// to them. For example, to assign a resolution to a [`Path`]. The [`NodeId`] is unique within a crate.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct NodeId(pub(super) usize);

impl NodeId {
    pub fn as_usize(&self) -> usize {
        self.0
    }
}

#[derive(Debug)]
pub struct SortDecl {
    pub name: Ident,
}

#[derive(Debug)]
pub enum Item {
    Qualifier(Qualifier),
    FuncDef(SpecFunc),
    SortDecl(SortDecl),
    PrimOpProp(PrimOpProp),
}

impl Item {
    pub fn name(&self) -> Ident {
        match self {
            Item::Qualifier(qualifier) => qualifier.name,
            Item::FuncDef(spec_func) => spec_func.name,
            Item::SortDecl(sort_decl) => sort_decl.name,
            Item::PrimOpProp(primop_prop) => primop_prop.name,
        }
    }
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: Ident,
    pub params: RefineParams,
    pub expr: Expr,
    pub span: Span,
    pub global: bool,
}

/// A global function definition. It can be either an uninterpreted function or a *syntactic abstraction*,
/// i.e., a function with a body.
#[derive(Debug)]
pub struct SpecFunc {
    pub name: Ident,
    pub sort_vars: Vec<Ident>,
    pub params: RefineParams,
    pub output: Sort,
    /// Body of the function. If not present this definition corresponds to an uninterpreted function.
    pub body: Option<Expr>,
    /// Is this function "hidden" i.e. to be considered
    /// as uninterpreted by default (only makes sense if `body` is_some ...)
    /// as otherwise it is *always* uninterpreted.
    pub hide: bool,
}

/// A (currently global) *primop property*; see tests/tests/pos/surface/
#[derive(Debug)]
pub struct PrimOpProp {
    /// The name of the property
    pub name: Ident,
    /// The binop it is attached to
    pub op: BinOp,
    /// The sort _at_ which the primop is defined,
    /// The binders for the inputs of the primop; the output sort is always `Bool`
    pub params: RefineParams,
    /// The actual definition of the property
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub predicates: Option<Vec<WhereBoundPredicate>>,
    pub span: Span,
}

#[derive(Debug)]
pub struct GenericParam {
    pub name: Ident,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct TyAlias {
    pub ident: Ident,
    pub generics: Generics,
    pub params: RefineParams,
    pub index: Option<RefineParam>,
    pub ty: Ty,
    pub node_id: NodeId,
    pub span: Span,
}

#[derive(Debug)]
pub struct ConstantInfo {
    pub expr: Option<Expr>,
}

#[derive(Debug)]
pub struct StructDef {
    pub generics: Option<Generics>,
    pub refined_by: Option<RefineParams>,
    pub fields: Vec<Option<Ty>>,
    pub opaque: bool,
    pub invariants: Vec<Expr>,
}

impl StructDef {
    /// Whether the struct contains any path that needs to be resolved.
    pub fn needs_resolving(&self) -> bool {
        self.fields.iter().any(Option::is_some)
    }
}

#[derive(Debug)]
pub struct EnumDef {
    pub generics: Option<Generics>,
    pub refined_by: Option<RefineParams>,
    pub variants: Vec<Option<VariantDef>>,
    pub invariants: Vec<Expr>,
    pub reflected: bool,
}

impl EnumDef {
    /// Whether the enum contains any path that needs to be resolved.
    pub fn needs_resolving(&self) -> bool {
        self.variants.iter().any(Option::is_some)
    }
}

#[derive(Debug)]
pub struct VariantDef {
    pub fields: Vec<Ty>,
    pub ret: Option<VariantRet>,
    pub node_id: NodeId,
    pub span: Span,
}

#[derive(Debug)]
pub struct VariantRet {
    pub path: Path,
    /// Binders are not allowed at this position, but we parse this as a list of indices
    /// for better error reporting.
    pub indices: Indices,
}

pub type RefineParams = Vec<RefineParam>;

#[derive(Debug, Default)]
pub struct QualNames {
    pub names: Vec<Ident>,
}

#[derive(Debug, Default)]
pub struct RevealNames {
    pub names: Vec<Ident>,
}

#[derive(Debug)]
pub struct RefineParam {
    pub ident: Ident,
    pub sort: Sort,
    pub mode: Option<ParamMode>,
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamMode {
    Horn,
    Hindley,
}

#[derive(Debug)]
pub enum Sort {
    /// A _base_ sort, e.g., `int` or `bool`.
    Base(BaseSort),
    /// A _function_ sort of the form `(bi,...) -> bo` where `bi..` and `bo`
    /// are all base sorts.
    Func { inputs: Vec<BaseSort>, output: BaseSort },
    /// A sort that needs to be inferred.
    Infer,
}

#[derive(Debug)]
pub enum BaseSort {
    /// a bitvector sort, e.g., bitvec<32>
    BitVec(u32),
    SortOf(Box<Ty>, Path),
    Path(SortPath),
}

/// A [`Path`] but for sorts.
#[derive(Debug)]
pub struct SortPath {
    /// The segments in the path
    pub segments: Vec<Ident>,
    /// The sort arguments, i.e., the list `[int, bool]` in `Map<int, bool>`.
    pub args: Vec<BaseSort>,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct Impl {
    pub generics: Option<Generics>,
    pub assoc_refinements: Vec<ImplAssocReft>,
}

#[derive(Debug)]
pub struct ImplAssocReft {
    pub name: Ident,
    pub params: RefineParams,
    pub output: BaseSort,
    pub body: Expr,
    pub span: Span,
}

pub struct Trait {
    pub generics: Option<Generics>,
    pub assoc_refinements: Vec<TraitAssocReft>,
}

#[derive(Debug)]
pub struct TraitAssocReft {
    pub name: Ident,
    pub params: RefineParams,
    pub output: BaseSort,
    pub body: Option<Expr>,
    pub span: Span,
    pub final_: bool,
}

#[derive(Debug)]
pub struct FnSpec {
    pub fn_sig: Option<FnSig>,
    pub qual_names: Option<QualNames>,
    pub reveal_names: Option<RevealNames>,
}

#[derive(Debug)]
pub struct FnSig {
    pub asyncness: Async,
    pub ident: Option<Ident>,
    pub generics: Generics,
    pub params: RefineParams,
    /// example: `requires n > 0`
    pub requires: Vec<Requires>,
    /// example: `i32<@n>`
    pub inputs: Vec<FnInput>,
    pub output: FnOutput,
    /// source span
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct Requires {
    /// Optional list of universally quantified parameters
    pub params: RefineParams,
    pub pred: Expr,
}

#[derive(Debug)]
pub struct FnOutput {
    /// example `i32{v:v >= 0}`
    pub returns: FnRetTy,
    /// example: `*x: i32{v. v = n+1}` or just `x > 10`
    pub ensures: Vec<Ensures>,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub enum Ensures {
    /// A type constraint on a location
    Type(Ident, Ty, NodeId),
    /// A predicate that needs to hold
    Pred(Expr),
}

#[derive(Debug)]
pub enum FnRetTy {
    Default(Span),
    Ty(Box<Ty>),
}

#[derive(Debug, Copy, Clone)]
pub enum Async {
    Yes { node_id: NodeId, span: Span },
    No,
}

#[derive(Debug)]
pub struct WhereBoundPredicate {
    pub span: Span,
    pub bounded_ty: Ty,
    pub bounds: GenericBounds,
}

pub type GenericBounds = Vec<TraitRef>;

#[derive(Debug)]
pub struct TraitRef {
    pub path: Path,
    pub node_id: NodeId,
}

impl TraitRef {
    fn is_fn_trait_name(name: Symbol) -> bool {
        name == sym::FnOnce || name == sym::FnMut || name == sym::Fn
    }

    pub fn as_fn_trait_ref(&self) -> Option<(&GenericArg, &GenericArg)> {
        if let [segment] = self.path.segments.as_slice()
            && Self::is_fn_trait_name(segment.ident.name)
            && let [in_arg, out_arg] = segment.args.as_slice()
        {
            return Some((in_arg, out_arg));
        }
        None
    }
}

#[derive(Debug)]
pub enum FnInput {
    /// example `a: i32{a > 0}`
    Constr(Ident, Path, Expr, NodeId),
    /// example `v: &strg i32`
    StrgRef(Ident, Ty, NodeId),
    /// A type with an optional binder, e.g, `i32`, `x: i32` or `x: i32{v: v > 0}`.
    /// The binder has a different meaning depending on the type.
    Ty(Option<Ident>, Ty, NodeId),
}

#[derive(Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub node_id: NodeId,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind {
    /// ty
    Base(BaseTy),
    /// `B[r]`
    Indexed {
        bty: BaseTy,
        indices: Indices,
    },
    /// B{v: r}
    Exists {
        bind: Ident,
        bty: BaseTy,
        pred: Expr,
    },
    GeneralExists {
        params: RefineParams,
        ty: Box<Ty>,
        pred: Option<Expr>,
    },
    /// Mutable or shared reference
    Ref(Mutability, Box<Ty>),
    /// Constrained type: an exists without binder
    Constr(Expr, Box<Ty>),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, ConstArg),
    /// The `NodeId` is used to resolve the type to a corresponding `OpaqueTy`
    ImplTrait(NodeId, GenericBounds),
    Hole,
}

impl Ty {
    pub fn is_refined(&self) -> bool {
        struct IsRefinedVisitor {
            is_refined: bool,
        }
        let mut vis = IsRefinedVisitor { is_refined: false };
        impl visit::Visitor for IsRefinedVisitor {
            fn visit_ty(&mut self, ty: &Ty) {
                match &ty.kind {
                    TyKind::Tuple(_)
                    | TyKind::Ref(..)
                    | TyKind::Array(..)
                    | TyKind::ImplTrait(..)
                    | TyKind::Hole
                    | TyKind::Base(_) => {
                        visit::walk_ty(self, ty);
                    }
                    TyKind::Indexed { .. }
                    | TyKind::Exists { .. }
                    | TyKind::GeneralExists { .. }
                    | TyKind::Constr(..) => {
                        self.is_refined = true;
                    }
                }
            }
        }
        vis.visit_ty(self);
        vis.is_refined
    }
}
#[derive(Debug)]
pub struct BaseTy {
    pub kind: BaseTyKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum BaseTyKind {
    Path(Option<Box<Ty>>, Path),
    Slice(Box<Ty>),
}

#[derive(PartialEq, Eq, Clone, Debug, Copy)]
pub struct ConstArg {
    pub kind: ConstArgKind,
    pub span: Span,
}

#[derive(PartialEq, Eq, Clone, Debug, Copy)]
pub enum ConstArgKind {
    Lit(usize),
    Infer,
}

#[derive(Debug)]
pub struct Indices {
    pub indices: Vec<RefineArg>,
    pub span: Span,
}

#[derive(Debug)]
pub enum RefineArg {
    /// `@n` or `#n`, the span corresponds to the span of the identifier plus the binder token (`@` or `#`)
    Bind(Ident, BindKind, Span, NodeId),
    Expr(Expr),
    Abs(RefineParams, Expr, Span, NodeId),
}

#[derive(Debug, Clone, Copy)]
pub enum BindKind {
    At,
    Pound,
}

#[derive(Debug)]
pub struct Path {
    pub segments: Vec<PathSegment>,
    pub refine: Vec<RefineArg>,
    pub node_id: NodeId,
    pub span: Span,
}

impl Path {
    pub fn last(&self) -> &PathSegment {
        self.segments
            .last()
            .expect("path must have at least one segment")
    }
}

#[derive(Debug)]
pub struct PathSegment {
    pub ident: Ident,
    pub args: Vec<GenericArg>,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct GenericArg {
    pub kind: GenericArgKind,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub enum GenericArgKind {
    Type(Ty),
    Constraint(Ident, Ty),
}

#[derive(Debug)]
pub struct FieldExpr {
    pub ident: Ident,
    pub expr: Expr,
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub struct Spread {
    pub expr: Expr,
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub enum ConstructorArg {
    FieldExpr(FieldExpr),
    Spread(Spread),
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub node_id: NodeId,
    pub span: Span,
}

#[derive(Debug)]
pub enum QuantKind {
    Forall,
    Exists,
}

#[derive(Debug)]
pub enum ExprKind {
    Path(ExprPath),
    Dot(Box<Expr>, Ident),
    Literal(Lit),
    BinaryOp(BinOp, Box<[Expr; 2]>),
    UnaryOp(UnOp, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    /// A UIF representing a PrimOp expression, e.g. `[<<](x, y)`
    PrimUIF(BinOp),
    /// `<qself as path>::name`
    AssocReft(Box<Ty>, Path, Ident),
    IfThenElse(Box<[Expr; 3]>),
    Constructor(Option<ExprPath>, Vec<ConstructorArg>),
    BoundedQuant(QuantKind, RefineParam, Range<usize>, Box<Expr>),
    Block(Vec<LetDecl>, Box<Expr>),
}

#[derive(Debug)]
pub struct LetDecl {
    pub param: RefineParam,
    pub init: Expr,
}

/// A [`Path`] but for refinement expressions
#[derive(Debug, Clone)]
pub struct ExprPath {
    pub segments: Vec<ExprPathSegment>,
    pub node_id: NodeId,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ExprPathSegment {
    pub ident: Ident,
    pub node_id: NodeId,
}
#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum BinOp {
    Iff,
    Imp,
    Or,
    And,
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitShl,
    BitShr,
}

impl fmt::Debug for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Iff => write!(f, "<=>"),
            BinOp::Imp => write!(f, "=>"),
            BinOp::Or => write!(f, "||"),
            BinOp::And => write!(f, "&&"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Ge => write!(f, ">="),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mod => write!(f, "mod"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::BitShl => write!(f, "<<"),
            BinOp::BitShr => write!(f, ">>"),
        }
    }
}

impl rustc_errors::IntoDiagArg for BinOp {
    fn into_diag_arg(self, _path: &mut Option<std::path::PathBuf>) -> rustc_errors::DiagArgValue {
        rustc_errors::DiagArgValue::Str(Cow::Owned(format!("{self:?}")))
    }
}

#[derive(Copy, Clone)]
pub enum UnOp {
    Not,
    Neg,
}

impl fmt::Debug for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Not => write!(f, "!"),
            Self::Neg => write!(f, "-"),
        }
    }
}

impl BindKind {
    pub fn token_str(&self) -> &'static str {
        match self {
            BindKind::At => "@",
            BindKind::Pound => "#",
        }
    }
}

/// A punctuated sequence of values of type `T` separated by punctuation of type `P`
pub struct Punctuated<T, P> {
    inner: Vec<(T, P)>,
    last: Option<Box<T>>,
}

impl<T, P> From<Vec<(T, P)>> for Punctuated<T, P> {
    fn from(inner: Vec<(T, P)>) -> Self {
        Self { inner, last: None }
    }
}

impl<T, P> Punctuated<T, P> {
    pub fn len(&self) -> usize {
        self.inner.len() + self.last.is_some() as usize
    }

    /// Determines whether this punctuated sequence is empty, meaning it
    /// contains no syntax tree nodes or punctuation.
    pub fn is_empty(&self) -> bool {
        self.inner.len() == 0 && self.last.is_none()
    }

    /// Appends a syntax tree node onto the end of this punctuated sequence. The
    /// sequence must already have a trailing punctuation, or be empty.
    ///
    /// # Panics
    ///
    /// Panics if the sequence is nonempty and does not already have a trailing
    /// punctuation.
    pub fn push_value(&mut self, value: T) {
        assert!(
            self.empty_or_trailing(),
            "Punctuated::push_value: cannot push value if Punctuated is missing trailing punctuation",
        );

        self.last = Some(Box::new(value));
    }

    /// Returns true if either this `Punctuated` is empty, or it has a trailing
    /// punctuation.
    ///
    /// Equivalent to `punctuated.is_empty() || punctuated.trailing_punct()`.
    pub fn empty_or_trailing(&self) -> bool {
        self.last.is_none()
    }

    /// Determines whether this punctuated sequence ends with a trailing
    /// punctuation.
    pub fn trailing_punct(&self) -> bool {
        self.last.is_none() && !self.is_empty()
    }

    pub fn into_values(self) -> Vec<T> {
        let mut v: Vec<T> = self.inner.into_iter().map(|(v, _)| v).collect();
        if let Some(last) = self.last {
            v.push(*last);
        }
        v
    }
}
