mod ast;
mod lexer;
mod resolve;

use lexer::{Lexer, LexerError, Token};
use resolve::resolve_ty;

use liquid_rust_common::ty::{Argument, Ty};

use lalrpop_util::lalrpop_mod;
use std::{fmt, ops::Range};

lalrpop_mod!(parser);

type LalrpopError<'source> = lalrpop_util::ParseError<usize, Token<'source>, LexerError>;

pub type ParseResult<T, Span = Range<usize>> = Result<T, ParseError<Span>>;

pub struct ParseError<Span = Range<usize>> {
    kind: ParseErrorKind,
    expected: Vec<String>,
    span: Span,
}

impl ParseError {
    fn new(kind: ParseErrorKind, expected: Vec<String>, span: Range<usize>) -> Self {
        Self {
            kind,
            expected,
            span,
        }
    }

    pub fn map_span<Span>(self, f: impl Fn(Range<usize>) -> Span) -> ParseError<Span> {
        ParseError {
            kind: self.kind,
            expected: self.expected,
            span: f(self.span),
        }
    }
}

impl<Span> ParseError<Span> {
    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn help(&self) -> Option<&'static str> {
        match &self.kind {
            ParseErrorKind::UnexpectedEOF => Some("there might be an unclosed delimiter."),
            ParseErrorKind::InvalidToken(token) => match token.as_str() {
                "=" => Some("maybe you meant `==`?"),
                _ => None,
            },
            _ => None,
        }
    }
}

impl<Span> fmt::Display for ParseError<Span> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ParseErrorKind::UnexpectedEOF => "type annotation ended unexpectedly.".fmt(f)?,
            ParseErrorKind::UnexpectedToken(token) => write!(f, "unexpected token `{}`.", token)?,
            ParseErrorKind::InvalidToken(token) => write!(f, "invalid token `{}`.", token)?,
            ParseErrorKind::UnboundedVariable(variable) => {
                write!(f, "unbounded variable `{}`.", variable)?
            }
        };

        match self.expected.as_slice() {
            [] => Ok(()),
            [head, tail @ ..] => {
                write!(f, "expected `{}`", head)?;
                for token in tail.iter().take(5) {
                    write!(f, ", `{}`", token)?;
                }
                write!(f, ".")
            }
        }
    }
}

pub enum ParseErrorKind {
    UnexpectedEOF,
    UnexpectedToken(String),
    InvalidToken(String),
    UnboundedVariable(String),
}

impl<'source> From<LalrpopError<'source>> for ParseError {
    fn from(err: LalrpopError<'source>) -> Self {
        match err {
            LalrpopError::InvalidToken { .. } => unreachable!(),
            LalrpopError::UnrecognizedEOF { location, expected } => {
                ParseError::new(ParseErrorKind::UnexpectedEOF, expected, location..location)
            }
            LalrpopError::UnrecognizedToken {
                token: (start, token, end),
                expected,
            } => ParseError::new(
                ParseErrorKind::UnexpectedToken(token.to_string()),
                expected,
                start..end,
            ),
            LalrpopError::ExtraToken {
                token: (start, token, end),
            } => ParseError::new(
                ParseErrorKind::UnexpectedToken(token.to_string()),
                vec![],
                start..end,
            ),
            LalrpopError::User {
                error: LexerError { token, span },
            } => ParseError::new(ParseErrorKind::InvalidToken(token), vec![], span),
        }
    }
}

pub fn parse_ty<'source>(source: &'source str) -> ParseResult<Ty<Argument>> {
    let lexer = Lexer::new(source);
    let ast_ty = parser::TyParser::new().parse(source, lexer)?;
    resolve_ty(&ast_ty)
}
