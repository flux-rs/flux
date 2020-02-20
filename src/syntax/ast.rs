extern crate syntax as rust_syntax;

pub use rust_syntax::ast::{AttrKind, AttrStyle, Attribute, IntTy, LitFloatType, LitIntType};
pub use rustc_hir::BodyId;
use rustc_hir::HirId;
pub use rustc_span::{symbol::Ident, Span, Symbol};
use std::collections::HashMap;
use std::fmt;

#[derive(Debug)]
pub struct BodyAnnots {
    pub body_id: BodyId,
    pub fn_ty: Option<FnType>,
    pub locals: HashMap<HirId, Reft>,
}

#[derive(Debug)]
pub struct FnType {
    pub inputs: Vec<Reft>,
    pub output: Reft,
}

#[derive(Debug)]
pub struct Reft {
    pub binding: Ident,
    pub hir_res: HirRes,
    pub pred: Pred,
    pub span: Span,
}

#[derive(Debug)]
pub struct Pred {
    pub expr_id: ExprId,
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct ExprId(pub(super) u32);

#[derive(Debug)]
pub enum ExprKind {
    Unary(UnOp, Box<Pred>),
    Binary(Box<Pred>, BinOp, Box<Pred>),
    Lit(Lit),
    Name(Name),
    Err,
}

#[derive(Debug)]
pub struct Lit {
    pub span: Span,
    pub kind: LitKind,
}

#[derive(Debug)]
pub enum LitKind {
    Bool(bool),
    Int(u128, LitIntType),
    Float(Symbol, LitFloatType),
    Err,
}

#[derive(Copy, Clone, Debug)]
pub struct UnOp {
    pub kind: UnOpKind,
    pub span: Span,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
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
    Binding(HirId),
    ReturnValue,
}

impl HirRes {
    pub fn hir_id(self) -> HirId {
        if let Self::Binding(hir_id) = self {
            hir_id
        } else {
            bug!("not a valid binding")
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct BinOp {
    pub kind: BinOpKind,
    pub span: Span,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
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

impl fmt::Debug for UnOpKind {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Deref => write!(fmt, "*"),
            Self::Not => write!(fmt, "!"),
        }
    }
}

impl fmt::Debug for BinOpKind {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::And => write!(fmt, "&&"),
            Self::Or => write!(fmt, "||"),
            Self::Eq => write!(fmt, "=="),
            Self::Lt => write!(fmt, "<"),
            Self::Gt => write!(fmt, ">"),
            Self::Ge => write!(fmt, ">="),
            Self::Mul => write!(fmt, "*"),
            Self::Div => write!(fmt, "/"),
            Self::Add => write!(fmt, "+"),
            Self::Sub => write!(fmt, "-"),
        }
    }
}
