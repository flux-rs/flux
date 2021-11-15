use std::fmt;

use liquid_rust_common::index::newtype_index;
pub use liquid_rust_fixpoint::Sort;
pub use liquid_rust_syntax::ast::BinOp;
pub use rustc_middle::ty::IntTy;
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
pub enum Ty {
    Refine(BaseTy, Expr),
    Exists(BaseTy, Name, Expr),
    MutRef(Ident),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BaseTy {
    Int(IntTy),
    Bool,
}

#[derive(Debug)]
pub struct Param {
    pub name: Ident,
    pub sort: Sort,
    pub pred: Expr,
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Option<Span>,
}

#[derive(Debug)]
pub enum ExprKind {
    Var(Ident),
    Literal(Lit),
    BinaryOp(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Copy, Debug)]
pub enum Lit {
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

impl Expr {
    pub const TRUE: Expr = Expr {
        kind: ExprKind::Literal(Lit::TRUE),
        span: None,
    };
}

impl Lit {
    pub const TRUE: Lit = Lit::Bool(true);

    pub fn sort(&self) -> Sort {
        match self {
            Lit::Int(_) => Sort::Int,
            Lit::Bool(_) => Sort::Bool,
        }
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
