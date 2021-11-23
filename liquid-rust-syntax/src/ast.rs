pub use rustc_ast::token::LitKind;
use rustc_span::{Span, Symbol};

#[derive(Debug)]
pub struct FnSig {
    pub generics: Generics,
    pub requires: Vec<(Ident, Ty)>,
    pub args: Vec<Ty>,
    pub ret: Ty,
    pub ensures: Vec<(Ident, Ty)>,
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
    RefineTy { path: Path, refine: Expr },
    Exists { bind: Ident, path: Path, pred: Expr },
    MutRef(Ident),
}

#[derive(Debug)]
pub struct Path {
    pub ident: Ident,
    pub args: Option<Vec<Ty>>,
    pub span: Span,
}

#[derive(Debug)]
pub enum GenericParam {
    Pure {
        name: Ident,
        sort: Ident,
        pred: Option<Expr>,
    },
    Type(Ident),
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
    Eq,
    Add,
    Lt,
    Le,
    Gt,
    Ge,
    Or,
    And,
}

#[derive(Debug, Clone, Copy)]
pub struct Ident {
    pub name: Symbol,
    pub span: Span,
}

impl Generics {
    pub fn empty(span: Span) -> Generics {
        Generics {
            params: vec![],
            span,
        }
    }
}
