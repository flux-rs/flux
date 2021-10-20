pub use rustc_ast::token::LitKind;
use rustc_span::{Span, Symbol};

#[derive(Debug)]
pub struct FnSig {
    pub params: Vec<Param>,
    pub args: Vec<Ty>,
    pub ret: Ty,
}

#[derive(Debug)]
pub struct Ty {
    pub name: Ident,
    pub refine: Refine,
}

#[derive(Debug)]
pub enum Refine {
    Var(Ident),
    Literal(Lit),
}

#[derive(Debug)]
pub struct Param {
    pub name: Ident,
    pub sort: Ident,
    pub pred: Expr,
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
}

#[derive(Debug)]
pub struct Ident {
    pub symbol: Symbol,
    pub span: Span,
}
