use std::{collections::VecDeque, iter::Peekable};

pub use rustc_ast::token::{BinOpToken, Delimiter, Lit, LitKind};
use rustc_ast::{
    token::{self, TokenKind},
    tokenstream::{RefTokenTreeCursor, TokenStream, TokenTree},
};
use rustc_span::{symbol::kw, BytePos, Symbol};

#[derive(Clone, Debug)]
pub enum Token {
    Caret,
    EqEq,
    Eq,
    AndAnd,
    OrOr,
    Plus,
    Minus,
    Slash,
    Not,
    Star,
    Colon,
    Comma,
    Semi,
    RArrow,
    Dot,
    Lt,
    Le,
    Ne,
    Gt,
    GtFollowedByGt,
    Ge,
    At,
    Pound,
    Fn,
    Async,
    Iff,
    FatArrow,
    Mut,
    Where,
    Impl,
    Requires,
    Ensures,
    Literal(Lit),
    Ident(Symbol),
    OpenDelim(Delimiter),
    CloseDelim(Delimiter),
    Invalid,
    Ref,
    And,
    Percent,
    Strg,
    Type,
    Ignore,
    Trusted,
    Check,
    If,
    Else,
    ModSep,
    Qualifier,
    Sort,
    Opaque,
    Local,
    BitVec,
    As,
    Refine,
}

pub(crate) struct Cursor<'t> {
    stack: Vec<Frame<'t>>,
    offset: BytePos,
    symbs: Symbols,
    tokens: VecDeque<(Location, Token, Location)>,
}

struct Symbols {
    fn_: Symbol,
    ref_: Symbol,
    requires: Symbol,
    ensures: Symbol,
    strg: Symbol,
    qualifier: Symbol,
    sort: Symbol,
    opaque: Symbol,
    local: Symbol,
    bitvec: Symbol,
    refine: Symbol,
}

struct Frame<'t> {
    cursor: Peekable<RefTokenTreeCursor<'t>>,
    close: Option<(Location, Token, Location)>,
}

#[derive(Clone, Copy, Debug)]
pub struct Location(pub(crate) BytePos);

impl<'t> Cursor<'t> {
    pub(crate) fn new(stream: &'t TokenStream, offset: BytePos) -> Self {
        Cursor {
            stack: vec![Frame { cursor: stream.trees().peekable(), close: None }],
            offset,
            tokens: VecDeque::new(),
            symbs: Symbols {
                fn_: Symbol::intern("fn"),
                ref_: Symbol::intern("ref"),
                strg: Symbol::intern("strg"),
                requires: Symbol::intern("requires"),
                ensures: Symbol::intern("ensures"),
                qualifier: Symbol::intern("qualifier"),
                sort: Symbol::intern("sort"),
                bitvec: Symbol::intern("bitvec"),
                opaque: Symbol::intern("opaque"),
                local: Symbol::intern("local"),
                refine: Symbol::intern("refine"),
            },
        }
    }

    fn map_token(&mut self, token: &token::Token) {
        let span = token.span;
        let token = match token.kind {
            TokenKind::Lt => Token::Lt,
            TokenKind::Le => Token::Le,
            TokenKind::EqEq => Token::EqEq,
            TokenKind::Eq => Token::Eq,
            TokenKind::Ne => Token::Ne,
            TokenKind::AndAnd => Token::AndAnd,
            TokenKind::OrOr => Token::OrOr,
            TokenKind::FatArrow => Token::FatArrow,
            TokenKind::Gt => Token::Gt,
            TokenKind::Ge => Token::Ge,
            TokenKind::At => Token::At,
            TokenKind::Pound => Token::Pound,
            TokenKind::Comma => Token::Comma,
            TokenKind::Colon => Token::Colon,
            TokenKind::Semi => Token::Semi,
            TokenKind::RArrow => Token::RArrow,
            TokenKind::Dot => Token::Dot,
            TokenKind::OpenDelim(delim) => Token::OpenDelim(delim),
            TokenKind::CloseDelim(delim) => Token::CloseDelim(delim),
            TokenKind::Literal(lit) => Token::Literal(lit),
            TokenKind::Ident(symb, _) if symb == kw::True || symb == kw::False => {
                Token::Literal(Lit { kind: LitKind::Bool, symbol: symb, suffix: None })
            }
            TokenKind::Ident(symb, _) if symb == self.symbs.ref_ => Token::Ref,
            TokenKind::Ident(symb, _) if symb == self.symbs.fn_ => Token::Fn,
            TokenKind::Ident(symb, _) if symb == self.symbs.strg => Token::Strg,
            TokenKind::Ident(symb, _) if symb == self.symbs.requires => Token::Requires,
            TokenKind::Ident(symb, _) if symb == self.symbs.ensures => Token::Ensures,
            TokenKind::Ident(symb, _) if symb == self.symbs.qualifier => Token::Qualifier,
            TokenKind::Ident(symb, _) if symb == self.symbs.sort => Token::Sort,
            TokenKind::Ident(symb, _) if symb == self.symbs.opaque => Token::Opaque,
            TokenKind::Ident(symb, _) if symb == self.symbs.local => Token::Local,
            TokenKind::Ident(symb, _) if symb == self.symbs.bitvec => Token::BitVec,
            TokenKind::Ident(symb, _) if symb == self.symbs.refine => Token::Refine,
            TokenKind::Ident(symb, _) if symb == kw::Mut => Token::Mut,
            TokenKind::Ident(symb, _) if symb == kw::Where => Token::Where,
            TokenKind::Ident(symb, _) if symb == kw::Impl => Token::Impl,
            TokenKind::Ident(symb, _) if symb == kw::Type => Token::Type,
            TokenKind::Ident(symb, _) if symb == kw::If => Token::If,
            TokenKind::Ident(symb, _) if symb == kw::Else => Token::Else,
            TokenKind::Ident(symb, _) if symb == kw::Async => Token::Async,
            TokenKind::Ident(symb, _) if symb == kw::As => Token::As,
            TokenKind::Ident(symb, _) => Token::Ident(symb),
            TokenKind::BinOp(BinOpToken::Or) => Token::Caret,
            TokenKind::BinOp(BinOpToken::Plus) => Token::Plus,
            TokenKind::BinOp(BinOpToken::Slash) => Token::Slash,
            TokenKind::BinOp(BinOpToken::Minus) => Token::Minus,
            TokenKind::BinOp(BinOpToken::And) => Token::And,
            TokenKind::BinOp(BinOpToken::Percent) => Token::Percent,
            TokenKind::BinOp(BinOpToken::Star) => Token::Star,
            TokenKind::BinOp(BinOpToken::Shr) => {
                self.push_token(span.lo(), Token::GtFollowedByGt, span.hi() - BytePos(1));
                self.push_token(span.lo() + BytePos(1), Token::Gt, span.hi());
                return;
            }
            TokenKind::Not => Token::Not,
            TokenKind::ModSep => Token::ModSep,
            _ => Token::Invalid,
        };
        self.push_token(span.lo(), token, span.hi());
    }

    fn push_token(&mut self, lo: BytePos, token: Token, hi: BytePos) {
        self.tokens
            .push_back((Location(lo - self.offset), token, Location(hi - self.offset)));
    }

    fn advance(&mut self) -> Option<()> {
        let top = self.stack.last_mut()?;

        match top.cursor.next() {
            Some(TokenTree::Token(token, _)) => {
                if let Some(TokenTree::Token(next, _)) = top.cursor.peek() {
                    match (&token.kind, &next.kind) {
                        (TokenKind::Le, TokenKind::Gt) if token.span.hi() == next.span.lo() => {
                            let lo = Location(token.span.lo() - self.offset);
                            let hi = Location(next.span.hi() - self.offset);
                            top.cursor.next();
                            self.tokens.push_back((lo, Token::Iff, hi));
                            return Some(());
                        }
                        _ => {}
                    }
                }
                self.map_token(token);
            }
            Some(TokenTree::Delimited(span, delim, tokens)) => {
                let close = (
                    Location(span.close.lo() - self.offset),
                    Token::CloseDelim(*delim),
                    Location(span.close.hi() - self.offset),
                );
                self.stack
                    .push(Frame { cursor: tokens.trees().peekable(), close: Some(close) });
                let token = token::Token { kind: TokenKind::OpenDelim(*delim), span: span.open };
                self.map_token(&token);
            }
            None => self.tokens.push_back(self.stack.pop()?.close?),
        }
        Some(())
    }
}

impl Iterator for Cursor<'_> {
    type Item = (Location, Token, Location);

    fn next(&mut self) -> Option<Self::Item> {
        if self.tokens.is_empty() {
            self.advance();
        }
        self.tokens.pop_front()
    }
}

impl Default for Location {
    fn default() -> Self {
        Location(BytePos(0))
    }
}
