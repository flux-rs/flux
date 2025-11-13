//! Support for "peeking" into the token stream to decide how to parse.

use std::fmt;

use rustc_span::{Symbol, edition::Edition};

use crate::{
    ParseCtxt, ParseError, ParseResult,
    surface::BinOp,
    symbols,
    token::{IdentIsRaw, Token, TokenKind},
};

/// See [`PeekExpected`]
#[derive(Debug)]
pub enum Expected {
    Str(&'static str),
    Sym(Symbol),
}

impl fmt::Display for Expected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expected::Str(descr) => write!(f, "{descr}"),
            Expected::Sym(sym) => write!(f, "{sym}"),
        }
    }
}

/// A trait for testing whether a token matches a rule.
pub(crate) trait Peek: Copy {
    /// Returns true if a token matches this rule
    ///
    /// The rule is edition dependent because keywords can vary.
    fn matches(self, tok: TokenKind, edition: Edition) -> bool;
}

/// A subtrait of [`Peek`] for rules that have an *expected description*.
///
/// This is used to automatically build error messages of the form:
/// ```text
/// expected one of `expected1`, `expected2`, ...
/// ```
/// where each `expected` is the description of a peek rule.
pub(crate) trait PeekExpected: Peek {
    fn expected(self) -> Expected;
}

/// Use a [`TokenKind`] to match by exact equality
impl Peek for TokenKind {
    fn matches(self, tok: TokenKind, _: Edition) -> bool {
        self == tok
    }
}
impl PeekExpected for TokenKind {
    fn expected(self) -> Expected {
        Expected::Str(TokenKind::descr(&self))
    }
}

/// A struct that can be used to match a non-reserved identifier
#[derive(Clone, Copy)]
pub(crate) struct NonReserved;
impl Peek for NonReserved {
    fn matches(self, tok: TokenKind, edition: Edition) -> bool {
        match tok {
            TokenKind::Ident(sym, IdentIsRaw::No) => !symbols::is_reserved(sym, edition),
            _ => false,
        }
    }
}
impl PeekExpected for NonReserved {
    fn expected(self) -> Expected {
        Expected::Str("identifier")
    }
}

/// A struct that can be used to match any literal
#[derive(Clone, Copy)]
pub(crate) struct AnyLit;
impl Peek for AnyLit {
    fn matches(self, tok: TokenKind, _: Edition) -> bool {
        matches!(tok, TokenKind::Literal(_))
    }
}
impl PeekExpected for AnyLit {
    fn expected(self) -> Expected {
        Expected::Str("literal")
    }
}

/// There are some lexing ambiguities with `>>` because it can represet both a right shift or two
/// closing angle brackets (e.g., `Vec<Option<i32>>`). We solve the ambiguity by giving `>` a
/// special token if it's immediately followed by another `>`,  i.e., `>>` is tokenized as
/// [`TokenKind::GtFollowedByGt`] followed by [`TokenKind::Gt`].
///
/// Use this struct to match on a right angle bracket for the purpose of parsing generics.
#[derive(Clone, Copy)]
pub(crate) struct RAngle;
impl Peek for RAngle {
    fn matches(self, tok: TokenKind, _: Edition) -> bool {
        matches!(tok, TokenKind::GtFollowedByGt | TokenKind::Gt)
    }
}
impl PeekExpected for RAngle {
    fn expected(self) -> Expected {
        Expected::Str(">")
    }
}

/// This is the same as [`RAngle`] but for opening angle brackets.
///
/// It is less common to have two opening angle brackets, but it appears in stuff like
/// `<<Self as Trait1>::Assoc1 as Trait2>::Assoc2`
#[derive(Clone, Copy)]
pub(crate) struct LAngle;
impl Peek for LAngle {
    fn matches(self, tok: TokenKind, _: Edition) -> bool {
        matches!(tok, TokenKind::LtFollowedByLt | TokenKind::Lt)
    }
}
impl PeekExpected for LAngle {
    fn expected(self) -> Expected {
        Expected::Str("<")
    }
}

/// Use a [`Symbol`] to match a [`TokenKind::Ident`] equal to it.
impl Peek for Symbol {
    fn matches(self, tok: TokenKind, _: Edition) -> bool {
        matches!(tok, TokenKind::Ident(sym, IdentIsRaw::No) if sym == self)
    }
}
impl PeekExpected for Symbol {
    fn expected(self) -> Expected {
        Expected::Sym(self)
    }
}

/// A rule that matches if any of the rules in a list matches
#[derive(Clone, Copy)]
pub(crate) struct AnyOf<T, const N: usize>(pub [T; N]);
impl<T: Peek, const N: usize> Peek for AnyOf<T, N> {
    fn matches(self, tok: TokenKind, edition: Edition) -> bool {
        self.0.into_iter().any(|t| t.matches(tok, edition))
    }
}

/// An arbitrary peek rule defined by a predicate on [`TokenKind`]
impl<F: FnOnce(TokenKind) -> bool + Copy> Peek for F {
    fn matches(self, tok: TokenKind, _: Edition) -> bool {
        (self)(tok)
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
    expected: Vec<Expected>,
    cx: &'a mut ParseCtxt<'cx>,
}

impl<'a, 'cx> Lookahead1<'a, 'cx> {
    fn new(cx: &'a mut ParseCtxt<'cx>) -> Self {
        Lookahead1 { expected: Vec::new(), cx }
    }

    /// Like [`ParseCtxt::peek`] but it records the expected token to construct an error in
    /// case parsing can't proceed. If this method returns true, this [`Lookahead1`] object should be
    /// discarded.
    pub(crate) fn peek<T: PeekExpected>(&mut self, t: T) -> bool {
        self.expected.push(t.expected());
        self.cx.peek(t)
    }

    /// Like [`ParseCtxt::advance_if`] but it records the expected token to construct an error in
    /// case parsing can't proceed. If this method returns true, this [`Lookahead1`] object should be
    /// discarded.
    pub(crate) fn advance_if<T: PeekExpected>(&mut self, t: T) -> bool {
        self.expected.push(t.expected());
        self.cx.advance_if(t)
    }

    /// Create an `unexpected token` error based on the expected tokens that have been peeked
    /// with this [`Lookahead1`] object.
    pub(crate) fn into_error(self) -> ParseError {
        self.cx.unexpected_token(self.expected)
    }
}

impl<'cx> ParseCtxt<'cx> {
    /// Returns the token at the requested position.
    pub(crate) fn at(&mut self, n: usize) -> Token {
        self.tokens.at(n)
    }

    /// Looks at the next token in the underlying cursor to determine whether it matches the
    /// requested type of token. Does not advance the position of the cursor.
    pub(crate) fn peek<T: Peek>(&mut self, t: T) -> bool {
        self.peek_at(0, t)
    }

    /// Looks at the next two tokens
    pub(crate) fn peek2<T1: Peek, T2: Peek>(&mut self, t1: T1, t2: T2) -> bool {
        self.peek_at(0, t1) && self.peek_at(1, t2)
    }

    /// Looks at the next three tokens
    pub(crate) fn peek3<T1: Peek, T2: Peek, T3: Peek>(&mut self, t1: T1, t2: T2, t3: T3) -> bool {
        self.peek_at(0, t1) && self.peek_at(1, t2) && self.peek_at(2, t3)
    }

    fn peek_at<T: Peek>(&mut self, n: usize, t: T) -> bool {
        let tok = self.at(n);
        t.matches(tok.kind, self.edition)
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
            TokenKind::Or => (BinOp::BitOr, 1),
            TokenKind::Caret => (BinOp::BitXor, 1),
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
    /// rule. Returns `true` if there was a match (i.e., the cursor was advanced).
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

    /// If the next token matches the requested rule advances the cursor, otherwise returns an
    /// `unexpected token` error.
    pub(crate) fn expect<T: PeekExpected>(&mut self, t: T) -> ParseResult {
        if self.advance_if(t) { Ok(()) } else { Err(self.unexpected_token(vec![t.expected()])) }
    }

    /// See documentation for [`Lookahead1`]
    pub(crate) fn lookahead1(&mut self) -> Lookahead1<'_, 'cx> {
        Lookahead1::new(self)
    }
}
