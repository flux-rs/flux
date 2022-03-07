pub use rustc_ast::token::LitKind;
pub use rustc_span::symbol::Ident;
use rustc_span::{Span, Symbol};

/* The concrete syntax for a function signature looks like

        fn<generics>(requires;args) -> ret;ensures

    For example, consider the signature

        fn ref_join<n: int, m: int{m > n}>(bool, i32@n, i32@m) -> i32{v: v >= 0}

        fn inc<n: int>(l: i32@n; ref<l>) -> (); l: i32 @ {n+1})

    The `generics` refers to the value binders for `n` and `m`

    The inputs are each a `Ty
*/

#[derive(Debug)]
pub struct FnSig {
    /// example: `<n: int>`
    pub generics: Generics,

    /// example: `l: i32@n`
    pub requires: Vec<(Ident, Ty)>,

    /// example: `bool, i32@n, i32@m`
    pub args: Vec<Ty>,

    /// example `i32{v:v >= 0}`
    pub ret: Ty,

    /// example: `l: i32 @ {n+1}`
    pub ensures: Vec<(Ident, Ty)>,

    pub span: Span,
}

#[derive(Debug)]
pub struct Qualifier {
    pub name: Ident,
    pub args: Vec<QualifParam>,
    pub expr: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind {
    BaseTy(Path),
    RefineTy { path: Path, refine: Refine },
    Exists { bind: Ident, path: Path, pred: Expr },
    StrgRef(Ident),
    WeakRef(Box<Ty>),
    ShrRef(Box<Ty>),
}

#[derive(Debug)]
pub struct Refine {
    pub exprs: Vec<Expr>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Path {
    pub ident: Ident,
    pub args: Option<Vec<Ty>>,
    pub span: Span,
}

/// `GenericParam` represents a "value" binder
#[derive(Debug)]
pub struct GenericParam {
    pub name: Ident,
    pub sort: Ident,
    pub pred: Option<Expr>,
}

/// `QualifParam` represents an "argument" in a qualifier
#[derive(Debug)]
pub struct QualifParam {
    pub name: Ident,
    pub sort: Ident,
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExprKind {
    Var(Ident),
    Literal(Lit),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub struct Lit {
    pub kind: LitKind,
    pub symbol: Symbol,
    pub span: Span,
}

#[derive(Debug, Copy, Clone)]
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
    Add,
    Sub,
    Mod,
    Mul,
}

impl Generics {
    pub fn empty(span: Span) -> Generics {
        Generics { params: vec![], span }
    }

    pub fn iter(&self) -> impl Iterator<Item = &GenericParam> {
        self.params.iter()
    }
}

impl IntoIterator for Generics {
    type Item = GenericParam;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.params.into_iter()
    }
}
