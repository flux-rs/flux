#![warn(unused_extern_crates)]
#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_span;

pub mod lexer;
pub mod surface;

use lalrpop_util::lalrpop_mod;
use lexer::{Cursor, Location, Token};
use rustc_ast::tokenstream::TokenStream;
use rustc_span::{def_id::LocalDefId, BytePos, Span, SyntaxContext};

lalrpop_mod!(
    #[allow(warnings)]
    #[allow(clippy::all)]
    grammar
);

struct ParseCtxt {
    offset: BytePos,
    ctx: SyntaxContext,
    parent: Option<LocalDefId>,
}

impl ParseCtxt {
    fn new(span: Span) -> Self {
        Self { offset: span.lo(), ctx: span.ctxt(), parent: span.parent() }
    }

    fn map_span(&self, lo: Location, hi: Location) -> Span {
        Span::new(lo.0 + self.offset, hi.0 + self.offset, self.ctx, self.parent)
    }

    fn map_err(&self, err: LalrpopError) -> ParseError {
        match err {
            LalrpopError::InvalidToken { .. } => unreachable!(),
            LalrpopError::User { error: UserParseError::UnexpectedToken(lo, hi) } => {
                ParseErrorKind::UnexpectedToken.into_error(self.map_span(lo, hi))
            }
            LalrpopError::UnrecognizedEof { location, expected: _ } => {
                ParseErrorKind::UnexpectedEof.into_error(self.map_span(location, location))
            }
            LalrpopError::UnrecognizedToken { token: (start, _, end), expected: _ }
            | LalrpopError::ExtraToken { token: (start, _, end) } => {
                ParseErrorKind::UnexpectedToken.into_error(self.map_span(start, end))
            }
        }
    }
}

macro_rules! parse {
    ($parser:path, $tokens:expr, $span:expr) => {{
        let mut cx = ParseCtxt::new($span);
        <$parser>::new()
            .parse(&mut cx, Cursor::new($tokens, $span.lo()))
            .map_err(|err| cx.map_err(err))
    }};
}

pub fn parse_refined_by(tokens: &TokenStream, span: Span) -> ParseResult<surface::RefinedBy> {
    parse!(grammar::RefinedByParser, tokens, span)
}

pub fn parse_type_alias(tokens: &TokenStream, span: Span) -> ParseResult<surface::TyAlias> {
    parse!(grammar::TyAliasParser, tokens, span)
}

pub fn parse_fn_sig(tokens: &TokenStream, span: Span) -> ParseResult<surface::FnSig> {
    parse!(grammar::FnSigParser, tokens, span)
}

pub fn parse_qual_names(tokens: &TokenStream, span: Span) -> ParseResult<surface::QualNames> {
    parse!(grammar::QualNamesParser, tokens, span)
}

pub fn parse_flux_item(tokens: &TokenStream, span: Span) -> ParseResult<Vec<surface::Item>> {
    parse!(grammar::ItemsParser, tokens, span)
}

pub fn parse_ty(tokens: &TokenStream, span: Span) -> ParseResult<surface::Ty> {
    parse!(grammar::TyParser, tokens, span)
}

pub fn parse_variant(tokens: &TokenStream, span: Span) -> ParseResult<surface::VariantDef> {
    parse!(grammar::VariantParser, tokens, span)
}

pub fn parse_expr(tokens: &TokenStream, span: Span) -> ParseResult<surface::Expr> {
    parse!(grammar::ExprParser, tokens, span)
}

pub enum UserParseError {
    UnexpectedToken(Location, Location),
}

type LalrpopError = lalrpop_util::ParseError<Location, Token, UserParseError>;

pub type ParseResult<T> = Result<T, ParseError>;

pub struct ParseError {
    pub kind: ParseErrorKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ParseErrorKind {
    UnexpectedEof,
    UnexpectedToken,
    IntTooLarge,
}

impl ParseErrorKind {
    fn into_error(self, span: Span) -> ParseError {
        ParseError { kind: self, span }
    }
}
