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
    pub ensures: Vec<(Ident, NamedTy)>,
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
    /// ty
    BaseTy(Path),
    /// ty{b:e} 
    Exists { bind: Ident, path: Path, pred: Expr },
}

#[derive(Debug)]
pub struct Path {
    /// vec
    pub ident: Ident,
    /// <nat>
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
    /// For inputs
    NamedBase(Ident, Ty),

    /// For outputs
    AnonBase(Ty),               

    /// For inputs and outputs
    Ref(RefKind, Box<NamedTy>),
}

#[derive(Debug)]
pub enum RefKind {
    Mut,
    Immut,
}