pub mod ast;
mod lexer;
pub mod resolution;
mod result;

use ast::Ty;
use lexer::Lexer;
pub use result::{ParseError, ParseErrorKind, ParseResult};
pub use lexer::Token;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser);

/// Parse a type annotation to produce an AST representation of a type with it.
pub fn parse_ty<'source>(source: &'source str) -> ParseResult<Ty<'source>> {
    let lexer = Lexer::new(source);
    parser::TyParser::new()
        .parse(source, lexer)
        .map_err(ParseError::from)
}
