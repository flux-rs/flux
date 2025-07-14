#![feature(rustc_private, box_patterns, new_range_api)]

extern crate rustc_ast;
extern crate rustc_errors;
extern crate rustc_span;

pub mod lexer;
mod parser;
pub mod surface;
pub mod symbols;

use lexer::{Cursor, TokenKind};
use rustc_ast::tokenstream::TokenStream;
use rustc_span::{BytePos, Span, Symbol, SyntaxContext, def_id::LocalDefId, edition::Edition};
use surface::NodeId;

use crate::parser::lookahead::Expected;

#[derive(Default)]
pub struct ParseSess {
    next_node_id: usize,
}

impl ParseSess {
    fn cx<'a>(&'a mut self, tokens: &'a TokenStream, span: Span) -> ParseCtxt<'a> {
        ParseCtxt::new(self, tokens, span)
    }

    pub fn parse_refined_by(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::RefineParams> {
        parser::parse_refined_by(&mut self.cx(tokens, span))
    }

    pub fn parse_type_alias(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::TyAlias> {
        parser::parse_type_alias(&mut self.cx(tokens, span))
    }

    pub fn parse_fn_sig(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::FnSig> {
        parser::parse_fn_sig(&mut self.cx(tokens, span))
    }

    pub fn parse_trait_assoc_reft(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<Vec<surface::TraitAssocReft>> {
        parser::parse_trait_assoc_refts(&mut self.cx(tokens, span))
    }

    pub fn parse_impl_assoc_reft(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<Vec<surface::ImplAssocReft>> {
        parser::parse_impl_assoc_refts(&mut self.cx(tokens, span))
    }

    pub fn parse_qual_names(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::QualNames> {
        parser::parse_qual_names(&mut self.cx(tokens, span))
    }

    pub fn parse_reveal_names(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::RevealNames> {
        parser::parse_reveal_names(&mut self.cx(tokens, span))
    }

    pub fn parse_flux_item(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<Vec<surface::Item>> {
        parser::parse_flux_items(&mut self.cx(tokens, span))
    }

    pub fn parse_type(&mut self, tokens: &TokenStream, span: Span) -> ParseResult<surface::Ty> {
        parser::parse_type(&mut self.cx(tokens, span))
    }

    pub fn parse_variant(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::VariantDef> {
        parser::parse_variant(&mut self.cx(tokens, span))
    }

    pub fn parse_expr(&mut self, tokens: &TokenStream, span: Span) -> ParseResult<surface::Expr> {
        parser::parse_expr(&mut self.cx(tokens, span), true)
    }

    pub fn parse_constant_info(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::ConstantInfo> {
        let expr = parser::parse_expr(&mut self.cx(tokens, span), true)?;
        Ok(surface::ConstantInfo { expr: Some(expr) })
    }

    pub fn parse_yes_or_no_with_reason(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<bool> {
        parser::parse_yes_or_no_with_reason(&mut self.cx(tokens, span))
    }

    pub fn next_node_id(&mut self) -> NodeId {
        let id = NodeId(self.next_node_id);
        self.next_node_id += 1;
        id
    }
}

struct ParseCtxt<'a> {
    sess: &'a mut ParseSess,
    ctx: SyntaxContext,
    parent: Option<LocalDefId>,
    edition: Edition,
    tokens: Cursor<'a>,
}

impl<'a> ParseCtxt<'a> {
    fn new(sess: &'a mut ParseSess, tokens: &'a TokenStream, span: Span) -> Self {
        Self {
            sess,
            ctx: span.ctxt(),
            parent: span.parent(),
            edition: span.edition(),
            tokens: Cursor::new(tokens, span.lo()),
        }
    }

    fn next_node_id(&mut self) -> NodeId {
        self.sess.next_node_id()
    }

    fn mk_span(&self, lo: BytePos, hi: BytePos) -> Span {
        Span::new(lo, hi, self.ctx, self.parent)
    }

    fn lo(&self) -> BytePos {
        self.tokens.lo()
    }

    fn hi(&self) -> BytePos {
        self.tokens.hi()
    }

    fn is_reserved(&self, sym: Symbol) -> bool {
        symbols::is_reserved(sym, self.edition)
    }

    fn unexpected_token(&mut self, expected: Vec<Expected>) -> ParseError {
        let tok = self.tokens.at(0);
        let kind = if tok.kind == TokenKind::Eof {
            ParseErrorKind::UnexpectedEof
        } else {
            ParseErrorKind::UnexpectedToken { expected }
        };
        ParseError { kind, span: self.mk_span(tok.lo, tok.hi) }
    }

    fn cannot_be_chained(&self, lo: BytePos, hi: BytePos) -> ParseError {
        ParseError { kind: ParseErrorKind::CannotBeChained, span: self.mk_span(lo, hi) }
    }
}

pub type ParseResult<T = ()> = Result<T, ParseError>;

pub struct ParseError {
    pub kind: ParseErrorKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ParseErrorKind {
    UnexpectedToken { expected: Vec<Expected> },
    UnexpectedEof,
    CannotBeChained,
    InvalidBinding,
    InvalidSort,
}
