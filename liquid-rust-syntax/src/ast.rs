pub use rustc_ast::token::LitKind;
pub use rustc_span::symbol::Ident;
use rustc_span::{Span, Symbol};

#[derive(Debug)]
pub struct FnSig {
    pub generics: Generics,
    pub requires: Vec<(Ident, Ty)>,
    pub args: Vec<Ty>,
    pub ret: Ty,
    pub ensures: Vec<(Ident, Ty)>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Generics {
    pub params: Vec<GenericParam>,
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
    RefineTy { path: Path, refine: Expr },
    Exists { bind: Ident, path: Path, pred: Expr },
    StrgRef(Ident),
    Ref(Box<Ty>),
}

#[derive(Debug)]
pub struct Path {
    pub ident: Ident,
    pub args: Option<Vec<Ty>>,
    pub span: Span,
}

#[derive(Debug)]
pub struct GenericParam {
    pub name: Ident,
    pub sort: Ident,
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

#[derive(Debug)]
pub struct Lit {
    pub kind: LitKind,
    pub symbol: Symbol,
    pub span: Span,
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Iff,
    Imp,
    Or,
    And,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mod,
}

impl Generics {
    pub fn empty(span: Span) -> Generics {
        Generics { params: vec![], span }
    }
}

impl IntoIterator for Generics {
    type Item = GenericParam;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.params.into_iter()
    }
}
