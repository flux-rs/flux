pub use liquid_rust_fixpoint::Sort;
pub use liquid_rust_syntax::ast::{BinaryOp, Ident};
pub use rustc_middle::ty::{IntTy, UintTy};
use rustc_span::Span;

#[derive(Debug)]
pub struct FnSig {
    pub params: Vec<(Ident, RType)>,
    pub args: Vec<Ty>,
    pub ret: Ty,
}

#[derive(Debug)]
pub enum Ty {
    Int(Expr, IntTy),
}

#[derive(Debug)]
pub struct RType {
    pub sort: Sort,
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
    BinaryOp(BinaryOp, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Copy, Debug)]
pub struct Lit {
    pub kind: LitKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub enum LitKind {
    Int(i128),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeLayout {
    Int(IntTy),
    Uint(UintTy),
}
