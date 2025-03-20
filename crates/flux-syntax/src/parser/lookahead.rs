//! Support for "peeking" into the token stream to decide how to parse.

use rustc_span::BytePos;

use crate::{
    ParseCtxt, ParseResult,
    lexer::{Cursor, Token},
    surface::BinOp,
};

/// A trait for testing whether a token matches a rule.
///
/// This trait is primarily implemented for [`Token`] to test for exact equality.
pub(crate) trait Peek {
    /// Returns true if the token at the requested position in the cursor matches this rule
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool;
}

impl Peek for Token {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        tokens.at(pos).1 == self
    }
}

/// A struct that can be used to match any identifier
pub(crate) struct AnyIdent;
impl Peek for AnyIdent {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Token::Ident(_))
    }
}

/// A struct that can be used to match any literal
pub(crate) struct AnyLit;
impl Peek for AnyLit {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Token::Literal(_))
    }
}

#[derive(Clone, Copy)]
pub(crate) struct LAngle;
impl Peek for LAngle {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Token::LtFollowedByLt | Token::Lt)
    }
}

#[derive(Clone, Copy)]
pub(crate) struct RAngle;
impl Peek for RAngle {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Token::GtFollowedByGt | Token::Gt)
    }
}

/// Use a string to match an identifier equal to it
impl Peek for &str {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        matches!(tokens.at(pos).1, Token::Ident(sym) if sym.as_str() == self)
    }
}

/// Use an array to match any token in a set
impl<T: Peek, const N: usize> Peek for [T; N] {
    fn peek_at(self, tokens: &mut Cursor, pos: usize) -> bool {
        self.into_iter().any(|t| t.peek_at(tokens, pos))
    }
}

impl ParseCtxt<'_> {
    /// Returns the token (and span) at the requested position.
    pub(crate) fn at(&mut self, n: usize) -> (BytePos, Token, BytePos) {
        self.tokens.at(n)
    }

    /// Looks at the next token in the underlying cursor to determine whether it matches the
    /// requested type of token. Does not advance the position of the cursor.
    pub(crate) fn peek<T: Peek>(&mut self, t: T) -> bool {
        t.peek_at(&mut self.tokens, 0)
    }

    /// Looks at the next two tokens
    pub(crate) fn peek2<T1: Peek, T2: Peek>(&mut self, t1: T1, t2: T2) -> bool {
        t1.peek_at(&mut self.tokens, 0) && t2.peek_at(&mut self.tokens, 1)
    }

    /// Looks at the next three tokens
    pub(crate) fn peek3<T1: Peek, T2: Peek, T3: Peek>(&mut self, t1: T1, t2: T2, t3: T3) -> bool {
        t1.peek_at(&mut self.tokens, 0)
            && t2.peek_at(&mut self.tokens, 1)
            && t3.peek_at(&mut self.tokens, 2)
    }

    /// Looks whether the next token matches a binary operation. In case of a match, returns
    /// the corresponding binary operation and its size in number of tokens. This function
    /// doesn't advance the position of the underlying cursor.
    pub(crate) fn peek_binop(&mut self) -> Option<(BinOp, usize)> {
        let op = match self.at(0).1 {
            Token::Iff => (BinOp::Iff, 1),
            Token::FatArrow => (BinOp::Imp, 1),
            Token::OrOr => (BinOp::Or, 1),
            Token::AndAnd => (BinOp::And, 1),
            Token::EqEq => (BinOp::Eq, 1),
            Token::Ne => (BinOp::Ne, 1),
            Token::Lt => (BinOp::Lt, 1),
            Token::Gt => (BinOp::Gt, 1),
            Token::Le => (BinOp::Le, 1),
            Token::Ge => (BinOp::Ge, 1),
            Token::Caret => (BinOp::BitOr, 1),
            Token::And => (BinOp::BitAnd, 1),
            Token::LtFollowedByLt => (BinOp::BitShl, 2),
            Token::GtFollowedByGt => (BinOp::BitShr, 2),
            Token::Plus => (BinOp::Add, 1),
            Token::Minus => (BinOp::Sub, 1),
            Token::Star => (BinOp::Mul, 1),
            Token::Slash => (BinOp::Div, 1),
            Token::Percent => (BinOp::Mod, 1),
            _ => return None,
        };
        Some(op)
    }

    /// Advances the underlying cursor to the next token
    pub(crate) fn advance(&mut self) {
        self.tokens.advance();
    }

    /// Advances the underlying cursor by the requested number of tokens
    pub(crate) fn advance_by(&mut self, n: usize) {
        self.tokens.advance_by(n);
    }

    /// Looks at the next token and advances the cursor if it matches the requested type of
    /// token. Returns `true` if there was a match.
    pub(crate) fn advance_if<T: Peek>(&mut self, t: T) -> bool {
        if self.peek(t) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Looks at the next two tokens advacing the cursor if there's a match on both of them
    pub(crate) fn advance_if2<T1: Peek, T2: Peek>(&mut self, t1: T1, t2: T2) -> bool {
        if self.peek2(t1, t2) {
            self.advance_by(2);
            true
        } else {
            false
        }
    }

    /// If the next token matches the requested type of token advances the cursor, otherwise
    /// returns an `unexpected token` error.
    pub(crate) fn expect<T: Peek>(&mut self, t: T) -> ParseResult {
        if self.advance_if(t) { Ok(()) } else { Err(self.unexpected_token()) }
    }
}
