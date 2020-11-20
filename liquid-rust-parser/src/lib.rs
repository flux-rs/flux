pub mod ast;
mod lexer;

use lexer::{Lexer, LexerError};
use ast::Ty;

use lalrpop_util::lalrpop_mod;
pub use lalrpop_util::ParseError;

lalrpop_mod!(parser);

pub type ParseResult<'source, T> = Result<T, ParseError<usize, lexer::Token<'source>, LexerError>>;

pub fn parse_ty<'source>(source: &'source str) -> ParseResult<'source, Ty<'source>> {
    let lexer = Lexer::new(source);
    parser::TyParser::new().parse(source, lexer)
}
