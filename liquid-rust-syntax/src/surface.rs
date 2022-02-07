pub use rustc_ast::token::LitKind;
pub use rustc_span::symbol::Ident;
use rustc_span::Span;

use crate::ast::Expr;

#[derive(Debug)]
pub struct FnSig {
    /// example: `l: i32@n`
    pub requires: Vec<(Ident, NamedTy)>,
    /// example `i32{v:v >= 0}`
    pub returns: Ty,
    /// example: `*x: i32{v:v = n+1}`
    pub ensures: Vec<(Ident, Ty)>,
    /// source span
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
    Exists { bind: Ident, path: Path, pred: Expr },
}

#[derive(Debug)]
pub struct Path {
    pub ident: Ident,
    pub args: Option<Vec<Ty>>,
    pub span: Span,
}

#[derive(Debug)]
pub struct NamedTy {
    pub kind: NamedTyKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum NamedTyKind {
    NamedBase(Ident, Ty),
    Ref(RefKind, Box<NamedTy>),
}

#[derive(Debug)]
pub enum RefKind {
    Mut,
    Immut,
}