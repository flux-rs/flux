use std::{collections::VecDeque, fmt, iter::Peekable};

pub use rustc_ast::token::{Delimiter, Lit, LitKind};
use rustc_ast::{
    token::InvisibleOrigin,
    tokenstream::{TokenStream, TokenStreamIter, TokenTree},
};
use rustc_span::{BytePos, Symbol};

use crate::symbols::kw;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum TokenKind {
    Caret,
    EqEq,
    Eq,
    AndAnd,
    OrOr,
    Plus,
    Minus,
    Slash,
    Bang,
    Star,
    Colon,
    Comma,
    Semi,
    RArrow,
    Dot,
    Le,
    Ne,
    GtFollowedByGt,
    Gt,
    LtFollowedByLt,
    Lt,
    Ge,
    At,
    Pound,
    Iff,
    FatArrow,
    Literal(Lit),
    /// This is used to represent both keywords and (non-reserved) identifiers
    Ident(Symbol),
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    OpenBracket,
    CloseBracket,
    OpenInvisible(InvisibleOrigin),
    CloseInvisible(InvisibleOrigin),
    Invalid,
    And,
    Percent,
    PathSep,
    DotDot,
    Eof,
}

#[derive(Clone, Copy)]
pub struct Token {
    pub kind: TokenKind,
    pub lo: BytePos,
    pub hi: BytePos,
}

impl Token {
    pub fn new(kind: TokenKind, lo: BytePos, hi: BytePos) -> Self {
        Self { kind, lo, hi }
    }
}

/// Convenience module so we can refer to token kinds as `token::*`
pub mod token {
    pub use super::TokenKind::*;
}

impl TokenKind {
    pub fn open_delim(delim: Delimiter) -> TokenKind {
        match delim {
            Delimiter::Parenthesis => token::OpenParen,
            Delimiter::Bracket => token::OpenBracket,
            Delimiter::Brace => token::OpenBrace,
            Delimiter::Invisible(origin) => token::OpenInvisible(origin),
        }
    }

    pub fn close_delim(delim: Delimiter) -> TokenKind {
        match delim {
            Delimiter::Parenthesis => token::CloseParen,
            Delimiter::Bracket => token::CloseBracket,
            Delimiter::Brace => token::CloseBrace,
            Delimiter::Invisible(origin) => token::CloseInvisible(origin),
        }
    }

    pub fn descr(&self) -> &'static str {
        match self {
            TokenKind::Caret => "|",
            TokenKind::EqEq => "==",
            TokenKind::Eq => "=",
            TokenKind::AndAnd => "&&",
            TokenKind::OrOr => "||",
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Slash => "/",
            TokenKind::Bang => "!",
            TokenKind::Star => "*",
            TokenKind::Colon => ":",
            TokenKind::Comma => ",",
            TokenKind::Semi => ";",
            TokenKind::RArrow => "->",
            TokenKind::Dot => ".",
            TokenKind::Le => "<=",
            TokenKind::Ne => ">=",
            TokenKind::GtFollowedByGt => ">",
            TokenKind::Gt => ">",
            TokenKind::LtFollowedByLt => "<",
            TokenKind::Lt => "<",
            TokenKind::Ge => ">=",
            TokenKind::At => "@",
            TokenKind::Pound => "#",
            TokenKind::Iff => "<=>",
            TokenKind::FatArrow => "=>",
            TokenKind::Literal(_) => "literal",
            TokenKind::Ident(_) => "identifier",
            TokenKind::OpenParen => "(",
            TokenKind::OpenBrace => "{",
            TokenKind::OpenBracket => "[",
            TokenKind::CloseParen => ")",
            TokenKind::CloseBrace => "}",
            TokenKind::CloseBracket => "]",
            TokenKind::OpenInvisible(_) => "",
            TokenKind::CloseInvisible(_) => "",
            TokenKind::And => "&",
            TokenKind::Percent => "%",
            TokenKind::PathSep => "::",
            TokenKind::DotDot => "..",
            TokenKind::Eof => "<eof>",
            TokenKind::Invalid => "<invalid>",
        }
    }

    pub fn is_keyword(self, kw: Symbol) -> bool {
        matches!(self, TokenKind::Ident(sym) if sym == kw)
    }

    pub fn is_eof(self) -> bool {
        matches!(self, TokenKind::Eof)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Literal(lit) => write!(f, "{lit}"),
            TokenKind::Ident(sym) => write!(f, "{sym}"),
            _ => write!(f, "{}", self.descr()),
        }
    }
}

pub struct Cursor<'t> {
    stack: Vec<Frame<'t>>,
    tokens: VecDeque<Token>,
    hi: BytePos,
}

struct Frame<'t> {
    cursor: Peekable<TokenStreamIter<'t>>,
    close: Option<Token>,
}

impl<'t> Cursor<'t> {
    pub(crate) fn new(stream: &'t TokenStream, offset: BytePos) -> Self {
        let mut cursor = Cursor {
            stack: vec![Frame { cursor: stream.iter().peekable(), close: None }],
            tokens: VecDeque::new(),
            hi: offset,
        };
        cursor.fetch_tokens();
        cursor
    }

    #[must_use]
    pub fn at(&mut self, pos: usize) -> Token {
        while self.tokens.len() <= pos && self.fetch_tokens() {}
        if pos < self.tokens.len() {
            self.tokens[pos]
        } else {
            Token::new(TokenKind::Eof, self.hi, self.hi)
        }
    }

    pub fn debug(&mut self, size: usize) -> String {
        let mut s = String::new();
        for i in 0..size {
            s = format!("{s} {}", self.at(i).kind);
        }
        s
    }

    pub fn advance(&mut self) {
        if let Some(tok) = self.tokens.pop_front() {
            if self.tokens.is_empty() {
                self.fetch_tokens();
            }
            self.hi = tok.hi;
        }
    }

    pub fn advance_by(&mut self, n: usize) {
        for _ in 0..n {
            self.advance();
        }
    }

    /// Returns the starting byte position of the next token
    pub fn lo(&self) -> BytePos {
        if let Some(tok) = self.tokens.front() { tok.lo } else { self.hi }
    }

    /// Returns the highest byte position the cursor has yielded. You could also think of this as
    /// the ending position of the last yielded token.
    pub fn hi(&self) -> BytePos {
        self.hi
    }

    fn map_token(&mut self, token: &rustc_ast::token::Token) {
        let span = token.span;
        let kind = match token.kind {
            rustc_ast::token::Lt => TokenKind::Lt,
            rustc_ast::token::Le => TokenKind::Le,
            rustc_ast::token::EqEq => TokenKind::EqEq,
            rustc_ast::token::Eq => TokenKind::Eq,
            rustc_ast::token::Ne => TokenKind::Ne,
            rustc_ast::token::AndAnd => TokenKind::AndAnd,
            rustc_ast::token::OrOr => TokenKind::OrOr,
            rustc_ast::token::FatArrow => TokenKind::FatArrow,
            rustc_ast::token::Gt => TokenKind::Gt,
            rustc_ast::token::Ge => TokenKind::Ge,
            rustc_ast::token::At => TokenKind::At,
            rustc_ast::token::Pound => TokenKind::Pound,
            rustc_ast::token::Comma => TokenKind::Comma,
            rustc_ast::token::Colon => TokenKind::Colon,
            rustc_ast::token::Semi => TokenKind::Semi,
            rustc_ast::token::RArrow => TokenKind::RArrow,
            rustc_ast::token::Dot => TokenKind::Dot,
            rustc_ast::token::OpenParen => TokenKind::OpenParen,
            rustc_ast::token::OpenBrace => TokenKind::OpenBrace,
            rustc_ast::token::OpenBracket => TokenKind::OpenBracket,
            rustc_ast::token::CloseParen => TokenKind::CloseParen,
            rustc_ast::token::CloseBrace => TokenKind::CloseBrace,
            rustc_ast::token::CloseBracket => TokenKind::CloseBracket,
            rustc_ast::token::OpenInvisible(origin) => TokenKind::OpenInvisible(origin),
            rustc_ast::token::CloseInvisible(origin) => TokenKind::CloseInvisible(origin),
            rustc_ast::token::Literal(lit) => TokenKind::Literal(lit),
            rustc_ast::token::Ident(symb, _) if symb == kw::True || symb == kw::False => {
                TokenKind::Literal(Lit { kind: LitKind::Bool, symbol: symb, suffix: None })
            }
            rustc_ast::token::Ident(symb, _) => TokenKind::Ident(symb),
            rustc_ast::token::NtIdent(ident, _) => TokenKind::Ident(ident.name),
            rustc_ast::token::Or => TokenKind::Caret,
            rustc_ast::token::Plus => TokenKind::Plus,
            rustc_ast::token::Slash => TokenKind::Slash,
            rustc_ast::token::Minus => TokenKind::Minus,
            rustc_ast::token::And => TokenKind::And,
            rustc_ast::token::Percent => TokenKind::Percent,
            rustc_ast::token::Star => TokenKind::Star,
            rustc_ast::token::Shl => {
                self.tokens.push_back(Token::new(
                    TokenKind::LtFollowedByLt,
                    span.lo(),
                    span.hi() - BytePos(1),
                ));
                self.tokens
                    .push_back(Token::new(TokenKind::Lt, span.lo() + BytePos(1), span.hi()));
                return;
            }
            rustc_ast::token::Shr => {
                self.tokens.push_back(Token::new(
                    TokenKind::GtFollowedByGt,
                    span.lo(),
                    span.hi() - BytePos(1),
                ));
                self.tokens
                    .push_back(Token::new(TokenKind::Gt, span.lo() + BytePos(1), span.hi()));
                return;
            }
            rustc_ast::token::Bang => TokenKind::Bang,
            rustc_ast::token::PathSep => TokenKind::PathSep,
            rustc_ast::token::DotDot => TokenKind::DotDot,
            _ => TokenKind::Invalid,
        };
        self.tokens
            .push_back(Token::new(kind, span.lo(), span.hi()));
    }

    fn fetch_tokens(&mut self) -> bool {
        let Some(top) = self.stack.last_mut() else { return false };

        match top.cursor.next() {
            Some(TokenTree::Token(token, _)) => {
                if let Some(TokenTree::Token(next, _)) = top.cursor.peek() {
                    match (&token.kind, &next.kind) {
                        (rustc_ast::token::Le, rustc_ast::token::Gt)
                            if token.span.hi() == next.span.lo() =>
                        {
                            top.cursor.next();
                            self.tokens.push_back(Token::new(
                                TokenKind::Iff,
                                token.span.lo(),
                                next.span.hi(),
                            ));
                            return true;
                        }
                        _ => {}
                    }
                }
                self.map_token(token);
                true
            }
            Some(TokenTree::Delimited(_, _spacing, Delimiter::Invisible(..), tokens)) => {
                self.stack
                    .push(Frame { cursor: tokens.iter().peekable(), close: None });
                self.fetch_tokens()
            }
            Some(TokenTree::Delimited(span, _spacing, delim, tokens)) => {
                let close_kind = match delim {
                    Delimiter::Parenthesis => TokenKind::CloseParen,
                    Delimiter::Brace => TokenKind::CloseBrace,
                    Delimiter::Bracket => TokenKind::CloseBracket,
                    Delimiter::Invisible(origin) => TokenKind::CloseInvisible(*origin),
                };
                let close = Token::new(close_kind, span.close.lo(), span.close.hi());

                self.stack
                    .push(Frame { cursor: tokens.iter().peekable(), close: Some(close) });

                let kind = match delim {
                    Delimiter::Parenthesis => rustc_ast::token::OpenParen,
                    Delimiter::Brace => rustc_ast::token::OpenBrace,
                    Delimiter::Bracket => rustc_ast::token::OpenBracket,
                    Delimiter::Invisible(origin) => rustc_ast::token::OpenInvisible(*origin),
                };

                let token = rustc_ast::token::Token { kind, span: span.open };
                self.map_token(&token);
                true
            }
            None => {
                let Some(frame) = self.stack.pop() else { return false };
                if let Some(token) = frame.close {
                    self.tokens.push_back(token);
                    true
                } else {
                    self.fetch_tokens()
                }
            }
        }
    }
}
