use liquid_rust_common::index::newtype_index;
pub use liquid_rust_fixpoint::Sort;
pub use liquid_rust_syntax::ast::BinOp;
use rustc_hir::def_id::DefId;
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
    Exists(BaseTy, Pred),
    MutRef(Ident),
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
    Bool,
    Adt(DefId, Vec<Ty>),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

impl BaseTy {
    pub fn sort(&self) -> Sort {
        match self {
            BaseTy::Int(_) => Sort::Int,
            BaseTy::Bool => Sort::Bool,
            BaseTy::Adt(_, _) => Sort::Int,
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

impl Pred {
    pub const TRUE: Pred = Pred::Expr(Expr::TRUE);
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
