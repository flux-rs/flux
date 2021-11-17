pub use rustc_ast::token::LitKind;
use rustc_span::{Span, Symbol};

#[derive(Debug)]
pub struct FnSig {
    pub params: Vec<Param>,
    pub requires: Vec<(Ident, Ty)>,
    pub args: Vec<Ty>,
    pub ret: Ty,
    pub ensures: Vec<(Ident, Ty)>,
}

#[derive(Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind {
    BaseTy(Ident),
    RefineTy { bty: Ident, refine: Expr },
    Exists { bind: Ident, bty: Ident, pred: Expr },
    MutRef(Ident),
    Param(Ident),
}

#[derive(Debug)]
pub enum Param {
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

#[derive(Debug)]
pub struct Ident {
    pub symbol: Symbol,
    pub span: Span,
}
