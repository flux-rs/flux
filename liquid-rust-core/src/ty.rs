use liquid_rust_common::index::newtype_index;
pub use liquid_rust_fixpoint::Sort;
pub use liquid_rust_syntax::ast::BinOp;
pub use rustc_middle::ty::IntTy;
use rustc_span::{Span, Symbol};

#[derive(Debug)]
pub struct FnSig {
    pub params: Vec<Param>,
    pub args: Vec<Ty>,
    pub ret: Ty,
}

#[derive(Debug)]
pub enum Ty {
    Refine(BaseTy, Refine),
    Exists(BaseTy, Name, Expr),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BaseTy {
    Int(IntTy),
}

#[derive(Debug)]
pub enum Refine {
    Var(Ident),
    Literal(Lit),
}

#[derive(Debug)]
pub struct Param {
    pub name: Ident,
    pub sort: Sort,
    pub pred: Option<Expr>,
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

#[derive(Clone, Copy, Debug)]
pub struct Lit {
    pub kind: LitKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub enum LitKind {
    Int(i128),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeLayout {
    Int(IntTy),
}

#[derive(Debug)]
pub struct Ident {
    pub name: Name,
    pub symbol: Symbol,
    pub span: Span,
}

newtype_index! {
    pub struct Name {
        DEBUG_FORMAT = "x{}",
    }
}

impl BaseTy {
    pub fn sort(&self) -> Sort {
        match self {
            BaseTy::Int(_) => Sort::Int,
        }
    }
}
