use logos::Logos;

/// Produce an interator of tokens from a slice.
pub fn tokenize<'ast>(source: &'ast str) -> impl Iterator<Item = LexerResult<'ast>> {
    RawToken::lexer(source)
        .spanned()
        .map(move |(raw_token, span)| {
            Token::from_raw(raw_token).ok_or_else(|| LexerError::new(&source[span]))
        })
}

/// Helper result type for lexing-related operations.
pub type LexerResult<'ast, T = Token<'ast>> = Result<T, LexerError<'ast>>;

/// Error for invalid tokens. It contains an slice with the invalid characters found by the lexer.
#[derive(Debug)]
pub struct LexerError<'ast> {
    slice: &'ast str,
}

impl<'ast> LexerError<'ast> {
    fn new(slice: &'ast str) -> Self {
        Self { slice }
    }
}

/// Valid tokens.
#[derive(Debug)]
pub enum Token<'ast> {
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
    Var(&'ast str),
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

impl<'ast> Token<'ast> {
    fn from_raw(raw_token: RawToken<'ast>) -> Option<Self> {
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
enum RawToken<'ast> {
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
    Var(&'ast str),
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

#[cfg(test)]
mod tests {
    use super::tokenize;
    #[test]
    fn it_works() {
        let lex = tokenize("fn(x: {x: usize | x > 0usize}, f: fn(y: {y: usize | y > 0usize}) -> {m: usize | m >= x + y}) -> {z: usize | z == f(x)}");
        for token in lex {
            print!("{:?} ", token);
        }
    }
}

