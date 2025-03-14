#![feature(rustc_private, box_patterns, let_chains, new_range_api)]

extern crate rustc_ast;
extern crate rustc_span;

pub mod lexer;
mod parser;
pub mod surface;

use lexer::Cursor;
use rustc_ast::tokenstream::TokenStream;
use rustc_span::{BytePos, Span, SyntaxContext, def_id::LocalDefId};
use surface::NodeId;

#[derive(Default)]
pub struct ParseSess {
    next_node_id: usize,
}

impl ParseSess {
    pub fn parse_refined_by(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::RefineParams> {
        ParseCtxt::new(self, span).parse_refined_by(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_generics(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::Generics> {
        ParseCtxt::new(self, span).parse_generics(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_type_alias(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::TyAlias> {
        ParseCtxt::new(self, span).parse_type_alias(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_fn_sig(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::FnSig> {
        ParseCtxt::new(self, span).parse_fn_sig(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_trait_assoc_reft(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<Vec<surface::TraitAssocReft>> {
        ParseCtxt::new(self, span).parse_trait_assoc_refts(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_impl_assoc_reft(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<Vec<surface::ImplAssocReft>> {
        ParseCtxt::new(self, span).parse_impl_assoc_refts(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_qual_names(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::QualNames> {
        ParseCtxt::new(self, span).parse_qual_names(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_flux_item(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<Vec<surface::Item>> {
        ParseCtxt::new(self, span).parse_flux_items(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_type(&mut self, tokens: &TokenStream, span: Span) -> ParseResult<surface::Ty> {
        ParseCtxt::new(self, span).parse_type(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_variant(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::VariantDef> {
        ParseCtxt::new(self, span).parse_variant(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn parse_expr(&mut self, tokens: &TokenStream, span: Span) -> ParseResult<surface::Expr> {
        ParseCtxt::new(self, span).parse_expr(&mut Cursor::new(tokens, span.lo()), true)
    }

    pub fn parse_constant_info(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<surface::ConstantInfo> {
        let expr =
            ParseCtxt::new(self, span).parse_expr(&mut Cursor::new(tokens, span.lo()), true)?;
        Ok(surface::ConstantInfo { expr: Some(expr) })
    }

    pub fn parse_yes_or_no_with_reason(
        &mut self,
        tokens: &TokenStream,
        span: Span,
    ) -> ParseResult<bool> {
        ParseCtxt::new(self, span).parse_yes_or_no_with_reason(&mut Cursor::new(tokens, span.lo()))
    }

    pub fn next_node_id(&mut self) -> NodeId {
        let id = NodeId(self.next_node_id);
        self.next_node_id += 1;
        id
    }
}

struct ParseCtxt<'a> {
    ctx: SyntaxContext,
    parent: Option<LocalDefId>,
    sess: &'a mut ParseSess,
}

impl<'a> ParseCtxt<'a> {
    fn new(sess: &'a mut ParseSess, span: Span) -> Self {
        Self { sess, ctx: span.ctxt(), parent: span.parent() }
    }

    fn next_node_id(&mut self) -> NodeId {
        self.sess.next_node_id()
    }

    fn mk_span(&self, lo: BytePos, hi: BytePos) -> Span {
        Span::new(lo, hi, self.ctx, self.parent)
    }
}

pub type ParseResult<T> = Result<T, ParseError>;

pub struct ParseError {
    pub kind: ParseErrorKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ParseErrorKind {
    UnexpectedEof,
    UnexpectedToken,
}

impl ParseErrorKind {
    fn into_error(self, span: Span) -> ParseError {
        ParseError { kind: self, span }
    }
}
