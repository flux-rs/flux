use std::fmt;

pub use rustc_ast::{
    token::{Lit, LitKind},
    Mutability,
};
pub use rustc_span::symbol::Ident;
use rustc_span::{symbol::kw, Span};

/// A [`NodeId`] is a unique identifier we assign to some AST nodes to be able to attach information
/// to them. For example, to assign a resolution to a [`Path`]. The [`NodeId`] is unique within a crate.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct NodeId(pub(super) usize);

#[derive(Debug)]
pub struct SortDecl {
    pub name: Ident,
}

#[derive(Debug)]
pub enum Item {
    Qualifier(Qualifier),
    FuncDef(FuncDef),
    SortDecl(SortDecl),
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: Ident,
    pub args: Vec<RefineParam>,
    pub expr: Expr,
    pub span: Span,
    pub global: bool,
}

/// A global function definition. It can be either an uninterpreted function or a *syntactic abstraction*,
/// i.e., a function with a body.
#[derive(Debug)]
pub struct FuncDef {
    pub name: Ident,
    pub args: Vec<RefineParam>,
    pub output: Sort,
    /// Body of the function. If not present this definition corresponds to an uninterpreted function.
    pub body: Option<Expr>,
}

#[derive(Debug)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub span: Span,
}

#[derive(Debug)]
pub struct GenericParam {
    pub name: Ident,
    pub kind: GenericParamKind,
}

#[derive(Debug)]
pub enum GenericParamKind {
    Type,
    Base,
    Refine { sort: Sort },
}

#[derive(Debug)]
pub struct TyAlias {
    pub ident: Ident,
    pub generics: Vec<Ty>,
    pub refined_by: RefinedBy,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug)]
pub struct StructDef {
    pub refined_by: Option<RefinedBy>,
    pub fields: Vec<Option<Ty>>,
    pub opaque: bool,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct EnumDef {
    pub refined_by: Option<RefinedBy>,
    pub variants: Vec<Option<VariantDef>>,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct VariantDef {
    pub fields: Vec<Ty>,
    pub ret: VariantRet,
    pub span: Span,
}

#[derive(Debug)]
pub struct VariantRet {
    pub path: Path,
    /// Binders are not allowed at this position, but we parse this as a list of indices
    /// for better error reporting.
    pub indices: Indices,
}

#[derive(Debug, Default)]
pub struct RefinedBy {
    pub early_bound_params: Vec<RefineParam>,
    pub index_params: Vec<RefineParam>,
    pub span: Span,
}

#[derive(Debug, Default)]
pub struct QualNames {
    pub names: Vec<Ident>,
}

#[derive(Debug)]
pub struct RefineParam {
    pub name: Ident,
    pub sort: Sort,
}

#[derive(Debug)]
pub enum Sort {
    /// A _base_ sort, e.g., `int` or `bool`.
    Base(BaseSort),
    /// A _function_ sort of the form `(bi,...) -> bo` where `bi..` and `bo`
    /// are all base sorts.
    Func {
        inputs: Vec<BaseSort>,
        output: BaseSort,
    },
    Infer,
}

#[derive(Debug, Clone)]
pub enum BaseSort {
    /// a _base_ sort, e.g. `int` or `bool`
    Ident(Ident),
    /// a bitvector sort, e.g., BitVec(32)
    BitVec(usize),
    /// a sort-constructor application, e.g., `Set<int>`
    App(Ident, Vec<BaseSort>),
}

#[derive(Debug)]
pub struct ConstSig {
    pub span: Span,
}

#[derive(Debug)]
pub struct FnSig {
    pub asyncness: Async,
    pub generics: Option<Generics>,
    /// example: `requires n > 0`
    pub requires: Option<Expr>,
    /// example: `i32<@n>`
    pub args: Vec<Arg>,
    /// example `i32{v:v >= 0}`
    pub returns: FnRetTy,
    /// example: `*x: i32{v. v = n+1}` or just `x > 10`
    pub ensures: Vec<Constraint>,
    /// example: `where I: Iterator<Item = i32{v:0<=v}>`
    pub predicates: Vec<WhereBoundPredicate>,
    /// source span
    pub span: Span,
}

#[derive(Debug)]
pub enum Constraint {
    /// A type constraint on a location
    Type(Ident, Ty),
    /// A predicate that needs to hold
    Pred(Expr),
}

#[derive(Debug)]
pub enum FnRetTy {
    Default(Span),
    Ty(Ty),
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
}

#[derive(Debug)]
pub enum Arg {
    /// example `a: i32{a > 0}`
    Constr(Ident, Path, Expr),
    /// example `v: &strg i32`
    StrgRef(Ident, Ty),
    /// A type with an optional binder, e.g, `i32`, `x: i32` or `x: i32{v: v > 0}`.
    /// The binder has a different meaning depending on the type.
    Ty(Option<Ident>, Ty),
}

#[derive(Debug)]
pub struct Ty {
    pub kind: TyKind,
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
        params: Vec<RefineParam>,
        ty: Box<Ty>,
        pred: Option<Expr>,
    },
    /// Mutable or shared reference
    Ref(Mutability, Box<Ty>),
    /// Constrained type: an exists without binder
    Constr(Expr, Box<Ty>),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, ArrayLen),
    /// The `NodeId` is used to resolve the type to a corresponding `OpaqueTy`
    ImplTrait(NodeId, GenericBounds),
}

#[derive(Debug)]
pub struct BaseTy {
    pub kind: BaseTyKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum BaseTyKind {
    Path(Path),
    Slice(Box<Ty>),
}

#[derive(Debug, Clone, Copy)]
pub struct ArrayLen {
    pub val: usize,
    pub span: Span,
}

#[derive(Debug)]
pub struct Indices {
    pub indices: Vec<RefineArg>,
    pub span: Span,
}

#[derive(Debug)]
pub enum RefineArg {
    /// `@n` or `#n`, the span corresponds to the span of the identifier plus the binder token (`@` or `#`)
    Bind(Ident, BindKind, Span),
    Expr(Expr),
    Abs(Vec<RefineParam>, Expr, Span),
}

#[derive(Debug, Clone, Copy)]
pub enum BindKind {
    At,
    Pound,
}

#[derive(Debug)]
pub struct Path {
    pub segments: Vec<Ident>,
    pub generics: Vec<GenericArg>,
    pub refine: Vec<RefineArg>,
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug)]
pub enum GenericArg {
    Type(Ty),
    Constraint(Ident, Ty),
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    QPath(QPathExpr),
    Dot(QPathExpr, Ident),
    Literal(Lit),
    BinaryOp(BinOp, Box<[Expr; 2]>),
    UnaryOp(UnOp, Box<Expr>),
    App(Ident, Vec<Expr>),
    IfThenElse(Box<[Expr; 3]>),
}

#[derive(Debug, Clone)]
pub struct QPathExpr {
    pub segments: Vec<Ident>,
    pub span: Span,
}

#[derive(Copy, Clone)]
pub enum BinOp {
    Iff,
    Imp,
    Or,
    And,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Ne,
    Add,
    Sub,
    Mod,
    Mul,
    Div,
}

#[derive(Copy, Clone, Debug)]
pub enum UnOp {
    Not,
    Neg,
}

impl Path {
    pub fn is_hole(&self) -> bool {
        if let [segment] = &self.segments[..] {
            segment.name == kw::Underscore && self.generics.is_empty() && self.refine.is_empty()
        } else {
            false
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

impl RefinedBy {
    pub fn all_params(&self) -> impl Iterator<Item = &RefineParam> {
        self.early_bound_params.iter().chain(&self.index_params)
    }
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
        }
    }
}
