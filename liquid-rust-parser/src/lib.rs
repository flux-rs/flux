pub mod ast;
mod lexer;
mod result;

use ast::FnDecl;
use lexer::Lexer;
pub use lexer::Token;
pub use result::{ParseError, ParseErrorKind, ParseResult};

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser);

/// Parse a function declaration annotation to produce an AST representation of a type with it.
pub fn parse_fn_decl<'source>(source: &'source str) -> ParseResult<FnDecl<'source>> {
    let lexer = Lexer::new(source);
    parser::FnDeclParser::new()
        .parse(source, lexer)
        .map_err(ParseError::from)
}
