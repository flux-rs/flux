use crate::ast::{ident::Ident, predicate::Predicate, Span};

// The AST representation of basic types.
#[derive(Debug, Copy, Clone)]
pub enum BaseTy {
    Bool,
    Int,
}

/// The AST representation of a refinement type.
#[derive(Debug)]
pub struct RefinedTy<'source> {
    pub variable: Ident<'source>,
    pub base_ty: BaseTy,
    pub refinement: Predicate<'source>,
}

#[derive(Debug)]
pub struct Ty<'source> {
    pub kind: TyKind<'source>,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind<'source> {
    Base(BaseTy),
    Refined(RefinedTy<'source>),
}

/// The AST representation of a dependent function type.
#[derive(Debug)]
pub struct FnDecl<'source> {
    pub inputs: Vec<(Ident<'source>, Ty<'source>)>,
    pub output: Option<Ty<'source>>,
    pub span: Span,
}
