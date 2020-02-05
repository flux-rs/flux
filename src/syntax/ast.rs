extern crate syntax as rust_syntax;

pub use rust_syntax::ast::{AttrKind, AttrStyle, Attribute, LitFloatType, LitIntType, LitKind};
use rustc_hir::HirId;
pub use rustc_hir::{BodyId, Lit};
pub use rustc_span::{symbol::Ident, Span};
use std::collections::HashMap;

#[derive(Debug)]
pub struct FnAnnots {
    pub body_id: BodyId,
    pub fn_ty: Option<FnType>,
    pub locals: HashMap<HirId, Refine>,
}

#[derive(Debug)]
pub struct FnType {
    pub inputs: Vec<Refine>,
    pub output: Refine,
}

#[derive(Debug)]
pub struct Refine {
    pub name: Name,
    pub pred: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct Expr {
    pub expr_id: ExprId,
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct ExprId(pub(super) u32);

#[derive(Debug)]
pub enum ExprKind {
    Unary(UnOp, Box<Expr>),
    Binary(Box<Expr>, BinOp, Box<Expr>),
    Lit(Lit),
    Name(Name),
    Err,
}

#[derive(Copy, Clone, Debug)]
pub struct UnOp {
    pub kind: UnOpKind,
    pub span: Span,
}

#[derive(Copy, Clone, Debug)]
pub enum UnOpKind {
    Deref,
    Not,
}

#[derive(Copy, Clone, Debug)]
pub struct Name {
    pub ident: Ident,
    pub hir_res: HirRes,
}

#[derive(Copy, Clone, Debug)]
pub enum HirRes {
    Unresolved,
    ExternalBinding(HirId, Span),
    CurrentBinding(HirId, Span),
    ReturnValue,
}

#[derive(Copy, Clone, Debug)]
pub struct BinOp {
    pub kind: BinOpKind,
    pub span: Span,
}

#[derive(Copy, Clone, Debug)]
pub enum BinOpKind {
    And,
    Or,

    Eq,
    Lt,
    Gt,
    Ge,

    Mul,
    Div,
    Add,
    Sub,
}
