use std::fmt;

pub use rustc_ast::token::{Lit, LitKind};
use rustc_hir::def_id::LocalDefId;
pub use rustc_hir::PrimTy;
pub use rustc_middle::ty::{FloatTy, IntTy, ParamTy, TyCtxt, UintTy};
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

pub type AliasMap = rustc_hash::FxHashMap<LocalDefId, Option<TyAlias>>;

#[derive(Debug)]
pub struct SortDecl {
    pub name: Ident,
}

#[derive(Debug)]
pub enum Item {
    Qualifier(Qualifier),
    Defn(Defn),
    Uif(UifDef),
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

#[derive(Debug)]
pub enum Def {
    Defn(Defn),
    UifDef(UifDef),
}

#[derive(Debug)]
pub struct Defn {
    pub name: Ident,
    pub args: Vec<RefineParam>,
    pub sort: Sort,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct UifDef {
    /// name of the uninterpreted function
    pub name: Ident,
    /// input sorts
    pub args: Vec<RefineParam>,
    /// output sort
    pub sort: Sort,
    /// definition source position
    pub span: Span,
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
    pub def_id: LocalDefId,
    pub refined_by: Option<RefinedBy>,
    pub fields: Vec<FieldDef<R>>,
    pub opaque: bool,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct FieldDef<R = ()> {
    pub def_id: LocalDefId,
    pub ty: Option<Ty<R>>,
}

#[derive(Debug)]
pub struct EnumDef<R = ()> {
    pub def_id: LocalDefId,
    pub refined_by: Option<RefinedBy>,
    pub variants: Vec<VariantDef<R>>,
    pub invariants: Vec<Expr>,
}

#[derive(Debug)]
pub struct VariantDef<R = ()> {
    pub def_id: LocalDefId,
    pub data: Option<VariantData<R>>,
}

#[derive(Debug)]
pub struct VariantData<R = ()> {
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
    Base(Ident),
    /// A _function_ sort of the form `(bi,...) -> bo` where `bi..` and `bo`
    /// are all base sorts.
    Func {
        inputs: Vec<Ident>,
        output: Ident,
    },
    Infer,
}

#[derive(Debug)]
pub struct ConstSig {
    pub span: Span,
}

#[derive(Debug)]
pub struct FnSig<R = ()> {
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
    /// source span
    pub span: Span,
}

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
    /// `t[e]`
    Indexed {
        bty: BaseTy<R>,
        indices: Indices,
    },
    /// ty{b:e}
    Exists {
        bind: Ident,
        bty: BaseTy<R>,
        pred: Expr,
    },
    /// Mutable or shared reference
    Ref(RefKind, Box<Ty<R>>),
    /// Constrained type: an exists without binder
    Constr(Expr, Box<Ty<R>>),
    Tuple(Vec<Ty<R>>),
    Array(Box<Ty<R>>, ArrayLen),
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
    pub generics: Vec<Ty<R>>,
    pub refine: Vec<RefineArg>,
    pub span: Span,
    pub res: R,
}

#[derive(Eq, PartialEq, Clone, Copy, Debug)]
pub enum RefKind {
    Mut,
    Shr,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Var(Ident),
    Dot(Box<Expr>, Ident),
    Literal(Lit),
    BinaryOp(BinOp, Box<[Expr; 2]>),
    UnaryOp(UnOp, Box<Expr>),
    App(Ident, Vec<Expr>),
    IfThenElse(Box<[Expr; 3]>),
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

    pub fn iter(&self) -> impl Iterator<Item = &RefineParam> {
        self.early_bound_params.iter().chain(&self.index_params)
    }
}

impl<'a> IntoIterator for &'a RefinedBy {
    type Item = &'a RefineParam;

    type IntoIter = impl Iterator<Item = &'a RefineParam>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
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
