pub mod ast;
pub mod mut_visit;
mod parser;
pub mod visit;

extern crate lalrpop_util;

use ast::{ExprId, FnType, Refine};
use parser::Token;
use parser::{FnRefinesParser, LocalRefineParser};
use rustc_span::{hygiene::SyntaxContext, BytePos, Span};
use std::cell::Cell;

pub type ParseError<'input> = lalrpop_util::ParseError<usize, Token<'input>, &'static str>;

pub struct ParsingCtxt {
    local_parser: LocalRefineParser,
    fn_parser: FnRefinesParser,
    next_expr_id: Cell<u32>,
}

impl ParsingCtxt {
    pub fn new() -> Self {
        ParsingCtxt {
            local_parser: LocalRefineParser::new(),
            fn_parser: FnRefinesParser::new(),
            next_expr_id: Cell::new(0),
        }
    }

    pub fn parse_local_annot<'a>(
        &mut self,
        span: Span,
        s: &'a str,
    ) -> Result<Refine, ParseError<'a>> {
        let next_expr_id = self.next_expr_id.clone();
        self.local_parser.parse(
            span.lo(),
            span.ctxt(),
            || {
                let id = next_expr_id.get();
                next_expr_id.set(id + 1);
                ExprId(id)
            },
            s,
        )
    }

    pub fn parse_fn_annot<'a>(&mut self, span: Span, s: &'a str) -> Result<FnType, ParseError<'a>> {
        let next_expr_id = self.next_expr_id.clone();
        self.fn_parser.parse(
            span.lo(),
            span.ctxt(),
            || {
                let id = next_expr_id.get();
                next_expr_id.set(id + 1);
                ExprId(id)
            },
            s,
        )
    }
}

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
