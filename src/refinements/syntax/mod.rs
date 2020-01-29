pub mod ast;
pub mod mut_visit;
pub mod parser;

extern crate lalrpop_util;

pub use parser::{FnRefinesParser, LocalRefineParser, Token};
use rustc_span::{hygiene::SyntaxContext, BytePos, Span};

pub type ParseError<'input> = lalrpop_util::ParseError<usize, Token<'input>, &'static str>;

pub fn err_span<'input>(err: &ParseError<'input>, offset: BytePos, ctxt: SyntaxContext) -> Span {
    let (lo, hi) = match err {
        ParseError::InvalidToken { location } | ParseError::UnrecognizedEOF { location, .. } => {
            (*location, *location)
        }

        ParseError::UnrecognizedToken {
            token: (lo, _, hi), ..
        }
        | ParseError::ExtraToken { token: (lo, _, hi) } => (*lo, *hi),

        ParseError::User { .. } => (0, 0),
    };
    span_with_offset(lo, hi, offset, ctxt)
}

pub fn err_msg<'input>(err: &ParseError<'input>) -> String {
    match *err {
        ParseError::User { error } => error.into(),
        ParseError::InvalidToken { .. } => "Invalid token".into(),
        ParseError::UnrecognizedEOF { .. } => "Unrecognized EOF".into(),
        ParseError::UnrecognizedToken { .. } => "Unexpected token".into(),
        ParseError::ExtraToken { .. } => "Extra token ".into(),
    }
}

pub fn span_with_offset(lo: usize, hi: usize, offset: BytePos, ctxt: SyntaxContext) -> Span {
    Span::new(
        offset + BytePos(lo as u32),
        offset + BytePos(hi as u32),
        ctxt,
    )
}
