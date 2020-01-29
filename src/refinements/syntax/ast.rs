use rustc::mir::Local;
use rustc_hir::HirId;
use rustc_span::{symbol::Symbol, Span};

#[derive(Debug)]
pub struct FnType {
    pub inputs: Vec<Refine>,
    pub output: Refine,
}

#[derive(Debug)]
pub struct Refine {
    pub binding: Ident,
    pub pred: Expr,
    pub span: Span,
}

#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExprKind {
    Unary(UnOp, Box<Expr>),
    Binary(Box<Expr>, BinOp, Box<Expr>),
    True,
    False,
    Int(i32),
    Ident(Ident),
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
pub struct Ident {
    pub span: Span,
    pub name: Symbol,
    pub hir_res: HirRes,
    pub mir_local: Option<Local>,
}

#[derive(Copy, Clone, Debug)]
pub enum HirRes {
    Unresolved,
    Binding(HirId),
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

    Lt,
    Gt,

    Mul,
    Div,
    Add,
    Sub,
}
