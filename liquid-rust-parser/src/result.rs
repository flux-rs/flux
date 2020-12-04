use crate::{
    ast::Span,
    lexer::{LexerError, Token},
};

type LalrpopError<'source> = lalrpop_util::ParseError<usize, Token<'source>, LexerError>;

pub type ParseResult<'source, T> = Result<T, ParseError<'source>>;

/// A parsing error.
pub struct ParseError<'source, S = Span> {
    /// Reason of the error.
    pub kind: ParseErrorKind<'source>,
    /// Tokens that the parser expected to find.
    pub expected: Vec<String>,
    pub span: S,
}

pub enum ParseErrorKind<'source> {
    /// Parsing failed because the type annotation ended too early.
    UnexpectedEOF,
    /// Parsing failed because there was an unexpected token.
    UnexpectedToken(Token<'source>),
}

impl<'source> ParseErrorKind<'source> {
    fn into_error(self, expected: Vec<String>, span: Span) -> ParseError<'source> {
        ParseError {
            kind: self,
            expected,
            span,
        }
    }
}

impl<'source> From<LalrpopError<'source>> for ParseError<'source> {
    fn from(err: LalrpopError<'source>) -> Self {
        match err {
            LalrpopError::InvalidToken { .. } | LalrpopError::User { .. } => unreachable!(),
            LalrpopError::UnrecognizedEOF { location, expected } => {
                ParseErrorKind::UnexpectedEOF.into_error(expected, location..location)
            }
            LalrpopError::UnrecognizedToken {
                token: (start, token, end),
                expected,
            } => ParseErrorKind::UnexpectedToken(token).into_error(expected, start..end),
            LalrpopError::ExtraToken {
                token: (start, token, end),
            } => ParseErrorKind::UnexpectedToken(token).into_error(vec![], start..end),
        }
    }
}
