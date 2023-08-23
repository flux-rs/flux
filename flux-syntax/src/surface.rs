use std::fmt;

pub use rustc_ast::{
    token::{Lit, LitKind},
    Mutability,
};
pub use rustc_span::symbol::Ident;
use rustc_span::{symbol::kw, Span};

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
pub struct TyAlias<R = ()> {
    pub ident: Ident,
    pub generics: Vec<Ty>,
    pub refined_by: RefinedBy,
    pub ty: Ty<R>,
    pub span: Span,
}

#[derive(Debug)]
pub struct StructDef<R = ()> {
    pub refined_by: Option<RefinedBy>,
    pub fields: Vec<Option<Ty<R>>>,
    pub opaque: bool,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct EnumDef<R = ()> {
    pub refined_by: Option<RefinedBy>,
    pub variants: Vec<Option<VariantDef<R>>>,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct VariantDef<R = ()> {
    pub fields: Vec<Ty<R>>,
    pub ret: VariantRet<R>,
    pub span: Span,
}

#[derive(Debug)]
pub struct VariantRet<R = ()> {
    pub path: Path<R>,
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
pub struct FnSig<R = ()> {
    pub asyncness: Async<R>,
    /// List of explicit refinement parameters
    pub params: Vec<RefineParam>,
    /// example: `requires n > 0`
    pub requires: Option<Expr>,
    /// example: `i32<@n>`
    pub args: Vec<Arg<R>>,
    /// example `i32{v:v >= 0}`
    pub returns: Option<Ty<R>>,
    /// example: `*x: i32{v. v = n+1}`
    pub ensures: Vec<(Ident, Ty<R>)>,
    /// example: `where I: Iterator<Item = i32{v:0<=v}>`
    pub predicates: Vec<WhereBoundPredicate<R>>,
    /// source span
    pub span: Span,
}

#[derive(Debug)]
pub enum Async<R = ()> {
    Yes { res: R, span: Span },
    No,
}

#[derive(Debug)]
pub struct WhereBoundPredicate<R = ()> {
    pub span: Span,
    pub bounded_ty: Ty<R>,
    pub bounds: Bounds<R>,
}

pub type Bounds<R = ()> = Vec<Path<R>>;

#[derive(Debug)]
pub enum Arg<R = ()> {
    /// example `a: i32{a > 0}`
    Constr(Ident, Path<R>, Expr),
    /// example `v: &strg i32`
    StrgRef(Ident, Ty<R>),
    /// A type with an optional binder, e.g, `i32`, `x: i32` or `x: i32{v: v > 0}`.
    /// The binder has a different meaning depending on the type.
    Ty(Option<Ident>, Ty<R>),
}

#[derive(Debug)]
pub struct Ty<R = ()> {
    pub kind: TyKind<R>,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind<R = ()> {
    /// ty
    Base(BaseTy<R>),
    /// `B[r]`
    Indexed {
        bty: BaseTy<R>,
        indices: Indices,
    },
    /// B{v: r}
    Exists {
        bind: Ident,
        bty: BaseTy<R>,
        pred: Expr,
    },
    GeneralExists {
        params: Vec<RefineParam>,
        ty: Box<Ty<R>>,
        pred: Option<Expr>,
    },
    /// Mutable or shared reference
    Ref(Mutability, Box<Ty<R>>),
    /// Constrained type: an exists without binder
    Constr(Expr, Box<Ty<R>>),
    Tuple(Vec<Ty<R>>),
    Array(Box<Ty<R>>, ArrayLen),
    /// The first `R` parameter is for the `DefId` corresponding to the hir OpaqueTy
    ImplTrait(R, Bounds<R>),
    Async(R, Box<Ty<R>>),
    Hole,
}

#[derive(Debug)]
pub struct BaseTy<R = ()> {
    pub kind: BaseTyKind<R>,
    pub span: Span,
}

#[derive(Debug)]
pub enum BaseTyKind<R = ()> {
    Path(Path<R>),
    Slice(Box<Ty<R>>),
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
pub struct Path<R = ()> {
    pub segments: Vec<Ident>,
    pub generics: Vec<GenericArg<R>>,
    pub refine: Vec<RefineArg>,
    pub span: Span,
    pub res: R,
}

#[derive(Debug)]
pub enum GenericArg<R = ()> {
    Type(Ty<R>),
    Constraint(Ident, Ty<R>),
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

impl From<Ident> for Path {
    fn from(ident: Ident) -> Self {
        Path { segments: vec![ident], generics: vec![], refine: vec![], span: ident.span, res: () }
    }
}

impl From<(Ident, Ident)> for Path {
    fn from(idents: (Ident, Ident)) -> Self {
        let (ident1, ident2) = idents;
        Path {
            segments: vec![ident1, ident2],
            generics: vec![],
            refine: vec![],
            span: ident1.span.to(ident2.span),
            res: (),
        }
    }
}

impl Path {
    pub fn is_hole(&self) -> bool {
        if let [segment] = &self.segments[..] {
            segment.name == kw::Underscore && self.is_simple()
        } else {
            false
        }
    }

    fn is_simple(&self) -> bool {
        self.generics.is_empty() && self.refine.is_empty()
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
    pub const DUMMY: &RefinedBy =
        &RefinedBy { index_params: vec![], early_bound_params: vec![], span: rustc_span::DUMMY_SP };

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

pub fn async_return_ty(ty: Ty) -> Ty {
    let span = ty.span;
    let kind = TyKind::Async((), Box::new(ty));
    Ty { kind, span }
}
