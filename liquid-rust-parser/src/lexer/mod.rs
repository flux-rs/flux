mod token;

pub use token::Token;

use logos::{Logos, SpannedIter};

/// Type for lexing errors.
///
/// This type is empty because lexing never fails under the conventions of the `lalrpop` crate.
/// Invalid tokens are still tokenized by the `logos` crate and have their own variant in the
/// `Token` enum.
#[derive(Debug)]
pub enum LexerError {}

/// A wrapper type for the `logos` lexer.
pub struct Lexer<'source> {
    /// The `logos` lexer for `Token`s.
    iter: SpannedIter<'source, Token<'source>>,
}

impl<'source> Lexer<'source> {
    /// Create a new lexer for a slice.
    pub fn new(source: &'source str) -> Self {
        Self {
            iter: Token::lexer(source).spanned(),
        }
    }
}

impl<'source> Iterator for Lexer<'source> {
    /// This is the result type required by the `lalrpop` crate.
    type Item = Result<(usize, Token<'source>, usize), LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        let (token, span) = self.iter.next()?;
        Some(Ok((span.start, token, span.end)))
    }
}
