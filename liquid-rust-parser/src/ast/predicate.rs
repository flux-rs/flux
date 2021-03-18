use crate::ast::{
    ident::Ident,
    op::{BinOp, UnOp},
    Span,
};

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
    /// A path.
    Path(Ident<'source>, Vec<usize>),
    /// An unary operation between predicates.
    UnaryOp(UnOp, Box<Predicate<'source>>),
    /// A binary operation between predicates.
    BinaryOp(BinOp, Box<Predicate<'source>>, Box<Predicate<'source>>),
}

#[derive(Debug)]
pub enum Literal {
    Bool(bool),
    Int(u128),
}
