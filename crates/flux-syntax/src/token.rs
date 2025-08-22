use std::fmt;

pub use TokenKind::*;
use rustc_ast::token::InvisibleOrigin;
pub use rustc_ast::token::{Delimiter, IdentIsRaw, Lit, LitKind};
use rustc_span::{BytePos, Symbol};

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum TokenKind {
    Caret,
    Or,
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
    Ident(Symbol, IdentIsRaw),
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

impl TokenKind {
    pub fn open_delim(delim: Delimiter) -> TokenKind {
        match delim {
            Delimiter::Parenthesis => TokenKind::OpenParen,
            Delimiter::Bracket => TokenKind::OpenBracket,
            Delimiter::Brace => TokenKind::OpenBrace,
            Delimiter::Invisible(origin) => TokenKind::OpenInvisible(origin),
        }
    }

    pub fn close_delim(delim: Delimiter) -> TokenKind {
        match delim {
            Delimiter::Parenthesis => TokenKind::CloseParen,
            Delimiter::Bracket => TokenKind::CloseBracket,
            Delimiter::Brace => TokenKind::CloseBrace,
            Delimiter::Invisible(origin) => TokenKind::CloseInvisible(origin),
        }
    }

    pub fn as_open_delim(&self) -> Option<Delimiter> {
        match self {
            Self::OpenParen => Some(Delimiter::Parenthesis),
            Self::OpenBrace => Some(Delimiter::Brace),
            Self::OpenBracket => Some(Delimiter::Bracket),
            _ => None,
        }
    }

    pub fn as_close_delim(&self) -> Option<Delimiter> {
        match self {
            Self::CloseParen => Some(Delimiter::Parenthesis),
            Self::CloseBrace => Some(Delimiter::Brace),
            Self::CloseBracket => Some(Delimiter::Bracket),
            _ => None,
        }
    }

    pub fn descr(&self) -> &'static str {
        match self {
            TokenKind::Caret => "^",
            TokenKind::Or => "|",
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
            TokenKind::Ident(..) => "identifier",
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
        matches!(self, TokenKind::Ident(sym, IdentIsRaw::No) if sym == kw)
    }

    pub fn is_eof(self) -> bool {
        matches!(self, TokenKind::Eof)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Literal(lit) => write!(f, "{lit}"),
            TokenKind::Ident(sym, _) => write!(f, "{sym}"),
            _ => write!(f, "{}", self.descr()),
        }
    }
}
