#![feature(rustc_private, box_patterns)]

extern crate rustc_ast;
extern crate rustc_span;

pub mod lexer;
pub mod surface;

use lalrpop_util::lalrpop_mod;
use lexer::{Cursor, Location, Token};
use rustc_ast::tokenstream::TokenStream;
use rustc_span::{def_id::LocalDefId, BytePos, Span, SyntaxContext};
use surface::NodeId;

lalrpop_mod!(
    #[allow(warnings)]
    #[allow(clippy::all)]
    grammar
);

#[derive(Default)]
pub struct ParseSess {
    next_node_id: usize,
}

macro_rules! parse {
    ($sess:expr, $parser:path, $tokens:expr, $span:expr) => {{
        let mut cx = ParseCtxt::new($sess, $span);
        <$parser>::new()
            .parse(&mut cx, Cursor::new($tokens, $span.lo()))
            .map_err(|err| cx.map_err(err))
    }};
}

impl ParseSess {
    pub fn parse_refined_by(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::RefineParams> {
        parse!(self, grammar::RefinedByParser, tokens, span)
    }

    pub fn parse_generics(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::Generics> {
        parse!(self, grammar::GenericsParser, tokens, span)
    }

    pub fn parse_type_alias(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::TyAlias> {
        parse!(self, grammar::TyAliasParser, tokens, span)
    }

    pub fn parse_fn_sig(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::FnSig> {
        parse!(self, grammar::FnSigParser, tokens, span)
    }

    pub fn parse_trait_assoc_reft(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::TraitAssocReft> {
        parse!(self, grammar::TraitAssocReftParser, tokens, span)
    }

    pub fn parse_impl_assoc_reft(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::ImplAssocReft> {
        parse!(self, grammar::ImplAssocReftParser, tokens, span)
    }

    pub fn parse_qual_names(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::QualNames> {
        parse!(self, grammar::QualNamesParser, tokens, span)
    }

    pub fn parse_flux_item(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<Vec<surface::Item>> {
        parse!(self, grammar::ItemsParser, tokens, span)
    }

    pub fn parse_type(&mut self, tokens: &TokenStream, span: Span) -> ParseResult<surface::Ty> {
        parse!(self, grammar::TyParser, tokens, span)
    }

    pub fn parse_variant(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::VariantDef> {
        parse!(self, grammar::VariantParser, tokens, span)
    }

    pub fn parse_expr(&mut self, tokens: &TokenStream, span: Span) -> ParseResult<surface::Expr> {
        parse!(self, grammar::ExprParser, tokens, span)
    }

    pub fn next_node_id(&mut self) -> NodeId {
        let id = NodeId(self.next_node_id);
        self.next_node_id += 1;
        id
    }
}

struct ParseCtxt<'a> {
    offset: BytePos,
    ctx: SyntaxContext,
    parent: Option<LocalDefId>,
    sess: &'a mut ParseSess,
}

impl<'a> ParseCtxt<'a> {
    fn new(sess: &'a mut ParseSess, span: Span) -> Self {
        Self { sess, offset: span.lo(), ctx: span.ctxt(), parent: span.parent() }
    }

    fn next_node_id(&mut self) -> NodeId {
        self.sess.next_node_id()
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
