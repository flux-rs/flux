use crate::ast::{
    ident::Ident,
    op::{BinOp, UnOp},
    Span,
};

use liquid_rust_mir::ty::Literal;

/// The AST representation of a quantifier-free predicate.
#[derive(Debug)]
pub struct Predicate<'source> {
    pub kind: PredicateKind<'source>,
    pub span: Span,
}

#[derive(Debug)]
pub enum PredicateKind<'source> {
    /// A literal.
    Lit(Literal),
    /// A variable.
    Var(Ident<'source>),
    /// An unary operation between predicates.
    UnaryOp(UnOp, Box<Predicate<'source>>),
    /// A binary operation between predicates.
    BinaryOp(BinOp, Box<Predicate<'source>>, Box<Predicate<'source>>),
}
