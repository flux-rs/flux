//! Support for "peeking" into the token stream to decide how to parse.

use crate::{
    ParseCtxt, ParseError, ParseResult,
    lexer::{Token, TokenKind},
    surface::BinOp,
};

/// A trait for testing whether a token matches a rule.
///
/// This trait is primarily implemented for [`TokenKind`] to test for exact equality.
pub(crate) trait Peek: Copy {
    /// Returns true if a token matches this rule
    fn matches(self, tok: TokenKind) -> bool;

    /// A string representation of the list of tokens matched by this rule. This
    /// is used to construct an error when using [`Lookahead1`].
    fn display(self) -> impl Iterator<Item = &'static str>;
}

impl Peek for TokenKind {
    fn matches(self, tok: TokenKind) -> bool {
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
    fn matches(self, tok: TokenKind) -> bool {
        matches!(tok, TokenKind::Ident(_))
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        ["identifier"].into_iter()
    }
}

/// A struct that can be used to match any literal
#[derive(Clone, Copy)]
pub(crate) struct AnyLit;
impl Peek for AnyLit {
    fn matches(self, tok: TokenKind) -> bool {
        matches!(tok, TokenKind::Literal(_))
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        ["literal"].into_iter()
    }
}

/// This is the same as [`RAngle`] but for opening angle brackets.
///
/// It is less common to have two opening angle brackets, but it appears in stuf like
/// `<<Self as Trait1>::Assoc1 as Trait2>::Assoc2`
#[derive(Clone, Copy)]
pub(crate) struct LAngle;
impl Peek for LAngle {
    fn matches(self, tok: TokenKind) -> bool {
        matches!(tok, TokenKind::LtFollowedByLt | TokenKind::Lt)
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        ["<"].into_iter()
    }
}

/// There are some lexing ambiguities with `>>` which can represet both a right shift or two
/// closing angle brackets in nested generics (e.g., `Vec<Option<i32>>`). We solve the ambiguity
/// by giving `>` a special token if it's immediately followed by another `>`,  i.e., `>>` is
/// tokenized as [`Token::GtFollowedByGt`] followed by [`Token::Gt`].
///
/// Use this struct to match on a right angle bracket for the purpose of parsing generics.
#[derive(Clone, Copy)]
pub(crate) struct RAngle;
impl Peek for RAngle {
    fn matches(self, tok: TokenKind) -> bool {
        matches!(tok, TokenKind::GtFollowedByGt | TokenKind::Gt)
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        [">"].into_iter()
    }
}

/// Use a string to match an identifier equal to it
impl Peek for &'static str {
    fn matches(self, tok: TokenKind) -> bool {
        matches!(tok, TokenKind::Ident(sym) if sym.as_str() == self)
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        [self].into_iter()
    }
}

/// Use an array to match any token in a set
impl<T: Peek, const N: usize> Peek for [T; N] {
    fn matches(self, tok: TokenKind) -> bool {
        self.into_iter().any(|t| t.matches(tok))
    }

    fn display(self) -> impl Iterator<Item = &'static str> {
        self.into_iter().flat_map(Peek::display)
    }
}

/// Support for checking the next token in a stream to decide how to parse.
///
/// An important advantage of using this struct over [`ParseCtxt::peek`] is that here we
/// automatically construct an appropriate error message based on the token alternatives
/// that get peeked.
///
/// Use [`ParseCtxt::lookahead1`] to construct this object.
pub(crate) struct Lookahead1<'a, 'cx> {
    /// List of "expected" tokens that have been peeked by this struct
    expected: Vec<&'static str>,
    cx: &'a mut ParseCtxt<'cx>,
}

impl<'a, 'cx> Lookahead1<'a, 'cx> {
    fn new(cx: &'a mut ParseCtxt<'cx>) -> Self {
        Lookahead1 { expected: Vec::new(), cx }
    }

    /// Like [`ParseCtxt::lookahead1`] but it records the expected token to construct an error in
    /// case parsing can't proceed. If this method returns true, this [`Lookahead1`] object should be
    /// discarded.
    pub(crate) fn peek<T: Peek>(&mut self, t: T) -> bool {
        self.expected.extend(t.display());
        self.cx.peek(t)
    }

    /// Like [`ParseCtxt::advance_if`] but it records the expected token to construct an error in
    /// case parsing can't proceed. If this method returns true, this [`Lookahead1`] object should be
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
    pub(crate) fn at(&mut self, n: usize) -> Token {
        self.tokens.at(n)
    }

    /// Looks at the next token in the underlying cursor to determine whether it matches the
    /// requested type of token. Does not advance the position of the cursor.
    pub(crate) fn peek<T: Peek>(&mut self, t: T) -> bool {
        t.matches(self.at(0).kind)
    }

    /// Looks at the next two tokens
    pub(crate) fn peek2<T1: Peek, T2: Peek>(&mut self, t1: T1, t2: T2) -> bool {
        t1.matches(self.at(0).kind) && t2.matches(self.at(1).kind)
    }

    /// Looks at the next three tokens
    pub(crate) fn peek3<T1: Peek, T2: Peek, T3: Peek>(&mut self, t1: T1, t2: T2, t3: T3) -> bool {
        t1.matches(self.at(0).kind) && t2.matches(self.at(1).kind) && t3.matches(self.at(2).kind)
    }

    /// Looks whether the next token matches a binary operation. In case of a match, returns
    /// the corresponding binary operation and its size in number of tokens. This function
    /// doesn't advance the position of the underlying cursor.
    pub(crate) fn peek_binop(&mut self) -> Option<(BinOp, usize)> {
        let op = match self.at(0).kind {
            TokenKind::Iff => (BinOp::Iff, 1),
            TokenKind::FatArrow => (BinOp::Imp, 1),
            TokenKind::OrOr => (BinOp::Or, 1),
            TokenKind::AndAnd => (BinOp::And, 1),
            TokenKind::EqEq => (BinOp::Eq, 1),
            TokenKind::Ne => (BinOp::Ne, 1),
            TokenKind::Lt => (BinOp::Lt, 1),
            TokenKind::Gt => (BinOp::Gt, 1),
            TokenKind::Le => (BinOp::Le, 1),
            TokenKind::Ge => (BinOp::Ge, 1),
            TokenKind::Caret => (BinOp::BitOr, 1),
            TokenKind::And => (BinOp::BitAnd, 1),
            TokenKind::LtFollowedByLt => (BinOp::BitShl, 2),
            TokenKind::GtFollowedByGt => (BinOp::BitShr, 2),
            TokenKind::Plus => (BinOp::Add, 1),
            TokenKind::Minus => (BinOp::Sub, 1),
            TokenKind::Star => (BinOp::Mul, 1),
            TokenKind::Slash => (BinOp::Div, 1),
            TokenKind::Percent => (BinOp::Mod, 1),
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

    /// Looks at the next token and advances the cursor if it matches the requested
    /// rule. Returns `true` if there was a match.
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

    /// See documentation for [`Lookahead1`]
    pub(crate) fn lookahead1(&mut self) -> Lookahead1<'_, 'cx> {
        Lookahead1::new(self)
    }
}
