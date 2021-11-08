use std::fmt;

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

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BaseTy {
    Int(IntTy),
    Bool,
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
    BaseTy(BaseTy),
    MutRef,
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
            BaseTy::Bool => Sort::Bool,
        }
    }

    /// Returns `true` if the base ty is [`Bool`].
    ///
    /// [`Bool`]: BaseTy::Bool
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }
}

impl fmt::Debug for BaseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(IntTy::I8) => write!(f, "i8"),
            Self::Int(IntTy::I16) => write!(f, "i16"),
            Self::Int(IntTy::I32) => write!(f, "i32"),
            Self::Int(IntTy::I64) => write!(f, "i64"),
            Self::Int(IntTy::I128) => write!(f, "i128"),
            Self::Int(IntTy::Isize) => write!(f, "isize"),
            Self::Bool => write!(f, "bool"),
        }
    }
}
