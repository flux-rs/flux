use std::fmt;

use liquid_rust_common::index::newtype_index;
pub use liquid_rust_syntax::ast::BinOp;
use rustc_hir::def_id::DefId;
pub use rustc_middle::ty::{IntTy, ParamTy, UintTy};
use rustc_span::{Span, Symbol};

pub struct AdtDef {
    pub refined_by: Vec<(Name, Sort)>,
}

#[derive(Debug)]
pub struct FnSig {
    pub params: Vec<Param>,
    pub requires: Vec<(Name, Ty)>,
    pub args: Vec<Ty>,
    pub ret: Ty,
    pub ensures: Vec<(Name, Ty)>,
}

#[derive(Debug)]
pub enum Ty {
    Refine(BaseTy, Expr),
    Exists(BaseTy, Pred),
    StrgRef(Name),
    WeakRef(Box<Ty>),
    ShrRef(Box<Ty>),
    Param(ParamTy),
}

#[derive(Debug)]
pub enum Pred {
    Infer,
    Expr(Expr),
}

#[derive(Debug)]
pub enum BaseTy {
    Int(IntTy),
    Uint(UintTy),
    Bool,
    Adt(DefId, Vec<Ty>),
}

#[derive(Debug)]
pub struct Param {
    pub name: Ident,
    pub sort: Sort,
    pub pred: Expr,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Sort {
    Bool,
    Int,
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub enum ExprKind {
    Var(Var, Symbol, Span),
    Literal(Lit),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum Var {
    Bound,
    Free(Name),
}

#[derive(Clone, Copy, Debug)]
pub enum Lit {
    Int(i128),
    Bool(bool),
}

#[derive(Debug, Clone, Copy)]
pub struct Ident {
    pub name: Name,
    pub source_info: (Span, Symbol),
}

newtype_index! {
    pub struct Name {
        DEBUG_FORMAT = "x{}",
    }
}

impl BaseTy {
    /// Returns `true` if the base ty is [`Bool`].
    ///
    /// [`Bool`]: BaseTy::Bool
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }
}

impl Expr {
    pub const TRUE: Expr = Expr { kind: ExprKind::Literal(Lit::TRUE), span: None };
}

impl Pred {
    pub const TRUE: Pred = Pred::Expr(Expr::TRUE);
}

impl Lit {
    pub const TRUE: Lit = Lit::Bool(true);
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "bool"),
            Sort::Int => write!(f, "int"),
        }
    }
}
