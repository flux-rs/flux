pub mod ast;
pub mod err;

pub use err::{ParseError, ParseErrorKind, ParseResult};
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(pub grammar);

/// Parse a type annotation to produce an AST representation of a type with it.
pub fn parse_ty<'source>(source: &'source str) -> err::ParseResult<ast::FnTy<'source>> {
    grammar::FnTyParser::new()
        .parse(source)
        .map_err(err::ParseError::from)
}
