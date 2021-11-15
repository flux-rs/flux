pub use rustc_ast::token::{BinOpToken, DelimToken, Lit, LitKind};
use rustc_ast::{
    token::{self, TokenKind},
    tokenstream::{self, TokenStream, TokenTree},
};
use rustc_span::{symbol::kw, BytePos, Symbol};

#[derive(Clone, Debug)]
pub enum Token {
    Caret,
    EqEq,
    AndAnd,
    OrOr,
    Plus,
    Colon,
    Comma,
    Semi,
    RArrow,
    Lt,
    Le,
    Gt,
    Ge,
    At,
    Fn,
    Literal(Lit),
    Ident(Symbol),
    OpenDelim(DelimToken),
    CloseDelim(DelimToken),
    Invalid,
    Ref,
}

pub(crate) struct Cursor {
    stack: Vec<Frame>,
    offset: BytePos,
    symbs: Symbols,
}

struct Symbols {
    fn_: Symbol,
    ref_: Symbol,
}

struct Frame {
    cursor: tokenstream::Cursor,
    close: Option<(Location, Token, Location)>,
}

#[derive(Clone, Copy, Debug)]
pub struct Location(pub(crate) BytePos);

impl Cursor {
    pub(crate) fn new(stream: TokenStream, offset: BytePos) -> Self {
        Cursor {
            stack: vec![Frame {
                cursor: stream.into_trees(),
                close: None,
            }],
            offset,
            symbs: Symbols {
                fn_: Symbol::intern("fn"),
                ref_: Symbol::intern("ref"),
            },
        }
    }

    fn map_token(&self, token: token::Token) -> (Location, Token, Location) {
        let span = token.span;
        let token = match token.kind {
            TokenKind::Lt => Token::Lt,
            TokenKind::Le => Token::Le,
            TokenKind::EqEq => Token::EqEq,
            TokenKind::AndAnd => Token::AndAnd,
            TokenKind::OrOr => Token::OrOr,
            TokenKind::Gt => Token::Gt,
            TokenKind::Ge => Token::Ge,
            TokenKind::At => Token::At,
            TokenKind::Comma => Token::Comma,
            TokenKind::Colon => Token::Colon,
            TokenKind::Semi => Token::Semi,
            TokenKind::RArrow => Token::RArrow,
            TokenKind::OpenDelim(delim) => Token::OpenDelim(delim),
            TokenKind::CloseDelim(delim) => Token::CloseDelim(delim),
            TokenKind::Literal(lit) if lit.suffix.is_none() => Token::Literal(lit),
            TokenKind::Ident(symb, _) if symb == kw::True || symb == kw::False => {
                Token::Literal(Lit {
                    kind: LitKind::Bool,
                    symbol: symb,
                    suffix: None,
                })
            }
            TokenKind::Ident(symb, _) if symb == self.symbs.ref_ => Token::Ref,
            TokenKind::Ident(symb, _) if symb == self.symbs.fn_ => Token::Fn,
            TokenKind::Ident(symb, _) => Token::Ident(symb),
            TokenKind::BinOp(BinOpToken::Or) => Token::Caret,
            TokenKind::BinOp(BinOpToken::Plus) => Token::Plus,
            _ => Token::Invalid,
        };
        (
            Location(span.lo() - self.offset),
            token,
            Location(span.hi() - self.offset),
        )
    }
}

impl Iterator for Cursor {
    type Item = (Location, Token, Location);

    fn next(&mut self) -> Option<Self::Item> {
        let top = self.stack.last_mut()?;

        match top.cursor.next() {
            Some(TokenTree::Token(token)) => Some(self.map_token(token)),
            Some(TokenTree::Delimited(span, delim, tokens)) => {
                let close = (
                    Location(span.close.lo() - self.offset),
                    Token::CloseDelim(delim),
                    Location(span.close.hi() - self.offset),
                );
                self.stack.push(Frame {
                    cursor: tokens.into_trees(),
                    close: Some(close),
                });
                Some(self.map_token(token::Token {
                    kind: TokenKind::OpenDelim(delim),
                    span: span.open,
                }))
            }
            None => self.stack.pop().unwrap().close,
        }
    }
}

impl Default for Location {
    fn default() -> Self {
        Location(BytePos(0))
    }
}
