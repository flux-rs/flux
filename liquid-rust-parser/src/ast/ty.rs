use crate::ast::{ident::Ident, predicate::Predicate, Span};

use liquid_rust_mir::ty::BaseTy;

/// The AST representation of a refinement type.
#[derive(Debug)]
pub struct Ty<'source> {
    pub kind: TyKind<'source>,
    pub span: Span,
}

#[derive(Debug)]
pub enum TyKind<'source> {
    /// An unrefined base type.
    Base(BaseTy),
    /// A refined base type.
    Refined(Ident<'source>, BaseTy, Predicate<'source>),
    /// A dependent function type.
    Func(Vec<(Ident<'source>, Ty<'source>)>, Box<Ty<'source>>),
}
