mod ast;
mod lexer;
mod resolve;

use lexer::{Lexer, LexerError};
use resolve::ResolveCtx;

use liquid_rust_common::ty::{Argument, Ty};

use lalrpop_util::lalrpop_mod;
pub use lalrpop_util::ParseError;

lalrpop_mod!(parser);

pub type ParseResult<'source, T> = Result<T, ParseError<usize, lexer::Token<'source>, LexerError>>;

pub fn parse_ty<'source>(source: &'source str) -> ParseResult<'source, Ty<Argument>> {
    let lexer = Lexer::new(source);
    let ast_ty = parser::TyParser::new().parse(source, lexer)?;
    let ty = ResolveCtx::default().resolve_ty(&ast_ty);

    Ok(ty)
}
