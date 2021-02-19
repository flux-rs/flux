use crate::ast::Span;

/// The ast representation of a variable's identifier.
#[derive(Debug)]
pub struct Ident<'source> {
    pub symbol: &'source str,
    pub span: Span,
}
