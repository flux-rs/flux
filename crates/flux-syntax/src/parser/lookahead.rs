//! Support for "peeking" into the token stream to decide how to parse.

use rustc_span::BytePos;

use crate::{ParseCtxt, ParseError, ParseResult, lexer::Token, surface::BinOp};

/// A trait for testing whether a token matches a rule.
///
/// This trait is primarily implemented for [`Token`] to test for exact equality.
pub(crate) trait Peek: Copy {
    /// Returns true if a token matches this rule
    fn matches(self, tok: Token) -> bool;

    fn display(self) -> impl Iterator<Item = &'static str>;
}

impl Peek for Token {
    fn matches(self, tok: Token) -> bool {
        self == tok
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        [self.descr()].into_iter()
    }
}

/// A struct that can be used to match any identifier
#[derive(Clone, Copy)]
pub(crate) struct AnyIdent;
impl Peek for AnyIdent {
    fn matches(self, tok: Token) -> bool {
        matches!(tok, Token::Ident(_))
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        ["identifier"].into_iter()
    }
}

/// A struct that can be used to match any literal
#[derive(Clone, Copy)]
pub(crate) struct AnyLit;
impl Peek for AnyLit {
    fn matches(self, tok: Token) -> bool {
        matches!(tok, Token::Literal(_))
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        ["literal"].into_iter()
    }
}

#[derive(Clone, Copy)]
pub(crate) struct LAngle;
impl Peek for LAngle {
    fn matches(self, tok: Token) -> bool {
        matches!(tok, Token::LtFollowedByLt | Token::Lt)
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        ["<"].into_iter()
    }
}

#[derive(Clone, Copy)]
pub(crate) struct RAngle;
impl Peek for RAngle {
    fn matches(self, tok: Token) -> bool {
        matches!(tok, Token::GtFollowedByGt | Token::Gt)
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        [">"].into_iter()
    }
}

/// Use a string to match an identifier equal to it
impl Peek for &'static str {
    fn matches(self, tok: Token) -> bool {
        matches!(tok, Token::Ident(sym) if sym.as_str() == self)
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        [self].into_iter()
    }
}

/// Use an array to match any token in a set
impl<T: Peek, const N: usize> Peek for [T; N] {
    fn matches(self, tok: Token) -> bool {
        self.into_iter().any(|t| t.matches(tok))
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        self.into_iter().flat_map(Peek::display)
    }
}

/// Support for checking the next token in a stream to decide how to parse.
///
/// An important advantage over [`ParseCtxt::peek`] is that here we automatically construct
/// an appropriate error message based on the token alternatives that get peeked.
///
/// Use [`ParseCtxt::lookahead1`] to construct this object.
pub(crate) struct Lookahead1<'a, 'cx> {
    expected: Vec<&'static str>,
    cx: &'a mut ParseCtxt<'cx>,
}

impl<'a, 'cx> Lookahead1<'a, 'cx> {
    fn new(cx: &'a mut ParseCtxt<'cx>) -> Self {
        Lookahead1 { expected: Vec::new(), cx }
    }

    /// Like [`ParseCtxt::lookahead1`] but it records the expected token to construct an error in
    /// case parsing can't proceed. If this method returns true, this [`Lookhead1`] object should be
    /// discarded.
    pub(crate) fn peek<T: Peek>(&mut self, t: T) -> bool {
        self.expected.extend(t.display());
        self.cx.peek(t)
    }

    /// Like [`ParseCtxt::advance_if`] but it records the expected token to construct an error in
    /// case parsing can't proceed. If this method returns true, this [`Lookhead1`] object should be
    /// discarded.
    pub(crate) fn advance_if<T: Peek>(&mut self, t: T) -> bool {
        self.expected.extend(t.display());
        self.cx.advance_if(t)
    }

    /// Create an `unexpected token` error based on the expected tokens that have been peeked
    /// with this [`Lookahead1`] object.
    pub(crate) fn into_error(self) -> ParseError {
        self.cx.unexpected_token(self.expected)
    }
}

impl<'cx> ParseCtxt<'cx> {
    /// Returns the token (and span) at the requested position.
    pub(crate) fn at(&mut self, n: usize) -> (BytePos, Token, BytePos) {
        self.tokens.at(n)
    }

    /// Looks at the next token in the underlying cursor to determine whether it matches the
    /// requested type of token. Does not advance the position of the cursor.
    pub(crate) fn peek<T: Peek>(&mut self, t: T) -> bool {
        t.matches(self.at(0).1)
    }

    /// Looks at the next two tokens
    pub(crate) fn peek2<T1: Peek, T2: Peek>(&mut self, t1: T1, t2: T2) -> bool {
        t1.matches(self.at(0).1) && t2.matches(self.at(1).1)
    }

    /// Looks at the next three tokens
    pub(crate) fn peek3<T1: Peek, T2: Peek, T3: Peek>(&mut self, t1: T1, t2: T2, t3: T3) -> bool {
        t1.matches(self.at(0).1) && t2.matches(self.at(1).1) && t3.matches(self.at(2).1)
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
        if self.advance_if(t) { Ok(()) } else { Err(self.unexpected_token(t.display().collect())) }
    }

    pub(crate) fn lookahead1(&mut self) -> Lookahead1<'_, 'cx> {
        Lookahead1::new(self)
    }
}
