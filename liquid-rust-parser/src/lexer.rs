use logos::{Logos, SpannedIter};

/// Helper result type for lexing-related operations.
pub type LexerResult<'source> = Result<(usize, Token<'source>, usize), LexerError>;

/// Error for invalid tokens.
#[derive(Debug)]
pub struct LexerError;

pub struct Lexer<'source> {
    iter: SpannedIter<'source, RawToken<'source>>,
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source str) -> Self {
        Self {
            iter: RawToken::lexer(source).spanned(),
        }
    }
}

impl<'source> Iterator for Lexer<'source> {
    type Item = LexerResult<'source>;

    fn next(&mut self) -> Option<Self::Item> {
        let (raw_token, span) = self.iter.next()?;
        Some(
            Token::from_raw(raw_token)
                .map(|token| (span.start, token, span.end))
                .ok_or(LexerError),
        )
    }
}

/// Valid tokens.
#[derive(Debug, Clone)]
pub enum Token<'source> {
    /// The `bool` token.
    Bool,
    /// The `u8` token.
    U8,
    /// The `u8` token.
    U16,
    /// The `u32` token.
    U32,
    /// The `u64` token.
    U64,
    /// The `u128` token.
    U128,
    /// The `usize` token.
    Usize,
    /// The `i8` token.
    I8,
    /// The `i8` token.
    I16,
    /// The `i32` token.
    I32,
    /// The `i64` token.
    I64,
    /// The `i128` token.
    I128,
    /// The `isize` token.
    Isize,
    /// The `true` token.
    True,
    /// The `false` token.
    False,
    /// An unsigned integer token.
    Integer(u128),
    /// A token for variables, it follows the rust reference for identifiers.
    Var(&'source str),
    /// The `fn` token.
    Fn,
    /// The `+` token.
    Add,
    /// The `-` token.
    Sub,
    /// The `*` token.
    Mul,
    /// The `&&` token.
    And,
    /// The `||` token.
    Or,
    /// The `!` token.
    Not,
    /// The `==` token.
    Eq,
    /// The `!=` token.
    Neq,
    /// The `>` token.
    Gt,
    /// The `<` token.
    Lt,
    /// The `>=` token.
    Gte,
    /// The `<=` token.
    Lte,
    /// The `(` token.
    OpenParen,
    /// The `)` token.
    CloseParen,
    /// The `{` token.
    OpenBracket,
    /// The `}` token.
    CloseBracket,
    /// The `|` token.
    Pipe,
    /// The `:` token.
    Colon,
    /// The `,` token.
    Comma,
    /// The `->` token.
    Arrow,
}

impl<'source> Token<'source> {
    fn from_raw(raw_token: RawToken<'source>) -> Option<Self> {
        match raw_token {
            RawToken::Bool => Some(Token::Bool),
            RawToken::U8 => Some(Token::U8),
            RawToken::U16 => Some(Token::U16),
            RawToken::U32 => Some(Token::U32),
            RawToken::U64 => Some(Token::U64),
            RawToken::U128 => Some(Token::U128),
            RawToken::Usize => Some(Token::Usize),
            RawToken::I8 => Some(Token::I8),
            RawToken::I16 => Some(Token::I16),
            RawToken::I32 => Some(Token::I32),
            RawToken::I64 => Some(Token::I64),
            RawToken::I128 => Some(Token::I128),
            RawToken::Isize => Some(Token::Isize),
            RawToken::True => Some(Token::True),
            RawToken::False => Some(Token::False),
            RawToken::Integer(integer) => Some(Token::Integer(integer)),
            RawToken::Var(slice) => Some(Token::Var(slice)),
            RawToken::Fn => Some(Token::Fn),
            RawToken::Add => Some(Token::Add),
            RawToken::Sub => Some(Token::Sub),
            RawToken::Mul => Some(Token::Mul),
            RawToken::And => Some(Token::And),
            RawToken::Or => Some(Token::Or),
            RawToken::Not => Some(Token::Not),
            RawToken::Eq => Some(Token::Eq),
            RawToken::Neq => Some(Token::Neq),
            RawToken::Gt => Some(Token::Gt),
            RawToken::Lt => Some(Token::Lt),
            RawToken::Gte => Some(Token::Gte),
            RawToken::Lte => Some(Token::Lte),
            RawToken::OpenParen => Some(Token::OpenParen),
            RawToken::CloseParen => Some(Token::CloseParen),
            RawToken::OpenBracket => Some(Token::OpenBracket),
            RawToken::CloseBracket => Some(Token::CloseBracket),
            RawToken::Pipe => Some(Token::Pipe),
            RawToken::Colon => Some(Token::Colon),
            RawToken::Comma => Some(Token::Comma),
            RawToken::Arrow => Some(Token::Arrow),
            RawToken::Error => None,
        }
    }
}

#[derive(Logos, Debug)]
enum RawToken<'source> {
    #[token("bool")]
    Bool,
    #[token("u8")]
    U8,
    #[token("u16")]
    U16,
    #[token("u32")]
    U32,
    #[token("u64")]
    U64,
    #[token("u128")]
    U128,
    #[token("usize")]
    Usize,
    #[token("i8")]
    I8,
    #[token("i16")]
    I16,
    #[token("i32")]
    I32,
    #[token("i64")]
    I64,
    #[token("i128")]
    I128,
    #[token("isize")]
    Isize,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[regex("[0-9]+", |lex| lex.slice().parse())]
    Integer(u128),
    #[regex("[a-zA-Z][a-zA-Z0-9_]*|_[a-zA-Z0-9_]+")]
    Var(&'source str),
    #[token("fn")]
    Fn,
    #[token("+")]
    Add,
    #[token("-")]
    Sub,
    #[token("*")]
    Mul,
    #[token("&&")]
    And,
    #[token("||")]
    Or,
    #[token("!")]
    Not,
    #[token("==")]
    Eq,
    #[token("!=")]
    Neq,
    #[token(">")]
    Gt,
    #[token("<")]
    Lt,
    #[token(">=")]
    Gte,
    #[token("<=")]
    Lte,
    #[token("(")]
    OpenParen,
    #[token(")")]
    CloseParen,
    #[token("{")]
    OpenBracket,
    #[token("}")]
    CloseBracket,
    #[token("|")]
    Pipe,
    #[token(":")]
    Colon,
    #[token(",")]
    Comma,
    #[token("->")]
    Arrow,
    #[error]
    #[regex(r"[ \t]+", logos::skip)]
    Error,
}
