use logos::Logos;
use std::fmt;

/// Tokens for the liquid rust's AST.
#[derive(Logos, Debug, Clone)]
pub enum Token<'source> {
    /// The `bool` token.
    #[token("bool")]
    Bool,
    /// The `u8` token.
    #[token("u8")]
    U8,
    /// The `u16` token.
    #[token("u16")]
    U16,
    /// The `u32` token.
    #[token("u32")]
    U32,
    /// The `u64` token.
    #[token("u64")]
    U64,
    /// The `u128` token.
    #[token("u128")]
    U128,
    /// The `usize` token.
    #[token("usize")]
    Usize,
    /// The `i8` token.
    #[token("i8")]
    I8,
    /// The `i16` token.
    #[token("i16")]
    I16,
    /// The `i32` token.
    #[token("i32")]
    I32,
    /// The `i64` token.
    #[token("i64")]
    I64,
    /// The `i128` token.
    #[token("i128")]
    I128,
    /// The `isize` token.
    #[token("isize")]
    Isize,
    /// The `true` token.
    #[token("true")]
    True,
    /// The `false` token.
    #[token("false")]
    False,
    /// An unsigned 8-bit integer token.
    #[regex("[0-9]+u8", |lex| lex.slice().trim_end_matches("u8").parse())]
    Uint8(u8),
    /// An unsigned 16-bit integer token.
    #[regex("[0-9]+u16", |lex| lex.slice().trim_end_matches("u16").parse())]
    Uint16(u16),
    /// An unsigned 32-bit integer token.
    #[regex("[0-9]+u32", |lex| lex.slice().trim_end_matches("u32").parse())]
    Uint32(u32),
    /// An unsigned 64-bit integer token.
    #[regex("[0-9]+u64", |lex| lex.slice().trim_end_matches("u64").parse())]
    Uint64(u64),
    /// An unsigned 128-bit integer token.
    #[regex("[0-9]+u128", |lex| lex.slice().trim_end_matches("u128").parse())]
    Uint128(u128),
    /// An unsigned pointer-sized integer token.
    #[regex("[0-9]+usize", |lex| lex.slice().trim_end_matches("usize").parse())]
    UintSize(usize),
    /// A signed 8-bit integer token.
    #[regex("[0-9]+i8", |lex| lex.slice().trim_end_matches("i8").parse())]
    Int8(i8),
    /// A signed 16-bit integer token.
    #[regex("-?[0-9]+i16", |lex| lex.slice().trim_end_matches("i16").parse())]
    Int16(i16),
    /// A signed 32-bit integer token.
    #[regex("-?[0-9]+i32", |lex| lex.slice().trim_end_matches("i32").parse())]
    Int32(i32),
    /// A signed 64-bit integer token.
    #[regex("-?[0-9]+i64", |lex| lex.slice().trim_end_matches("i64").parse())]
    Int64(i64),
    /// A signed 128-bit integer token.
    #[regex("-?[0-9]+i128", |lex| lex.slice().trim_end_matches("i128").parse())]
    Int128(i128),
    /// A signed pointer-sized integer token.
    #[regex("-?[0-9]+isize", |lex| lex.slice().trim_end_matches("isize").parse())]
    IntSize(isize),
    /// A token for variable names.
    ///
    /// It follows the same rules as the rust reference for valid identifiers.
    #[regex("[a-zA-Z][a-zA-Z0-9_]*|_[a-zA-Z0-9_]+")]
    Ident(&'source str),
    /// The `fn` token.
    #[token("fn")]
    Fn,
    /// The `+` token.
    #[token("+")]
    Add,
    /// The `-` token.
    #[token("-")]
    Sub,
    /// The `*` token.
    #[token("*")]
    Mul,
    /// The `/` token.
    #[token("/")]
    Div,
    /// The `%` token.
    #[token("%")]
    Rem,
    /// The `&&` token.
    #[token("&&")]
    And,
    /// The `||` token.
    #[token("||")]
    Or,
    /// The `!` token.
    #[token("!")]
    Not,
    /// The `==` token.
    #[token("==")]
    Eq,
    /// The `!=` token.
    #[token("!=")]
    Neq,
    /// The `>` token.
    #[token(">")]
    Gt,
    /// The `<` token.
    #[token("<")]
    Lt,
    /// The `>=` token.
    #[token(">=")]
    Gte,
    /// The `<=` token.
    #[token("<=")]
    Lte,
    /// The `(` token.
    #[token("(")]
    OpenParen,
    /// The `)` token.
    #[token(")")]
    CloseParen,
    /// The `{` token.
    #[token("{")]
    OpenBracket,
    /// The `}` token.
    #[token("}")]
    CloseBracket,
    /// The `|` token.
    #[token("|")]
    Pipe,
    /// The `:` token.
    #[token(":")]
    Colon,
    /// The `,` token.
    #[token(",")]
    Comma,
    /// The `->` token.
    #[token("->")]
    Arrow,
    /// An invalid token.
    #[error]
    #[regex(r"[ \t]+", logos::skip)]
    Invalid,
}

impl<'source> fmt::Display for Token<'source> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Token::*;

        match self {
            Bool => "bool".fmt(f),
            U8 => "u8".fmt(f),
            U16 => "u16".fmt(f),
            U32 => "u32".fmt(f),
            U64 => "u64".fmt(f),
            U128 => "u128".fmt(f),
            Usize => "usize".fmt(f),
            I8 => "i8".fmt(f),
            I16 => "i64".fmt(f),
            I32 => "i32".fmt(f),
            I64 => "i64".fmt(f),
            I128 => "i128".fmt(f),
            Isize => "isize".fmt(f),
            True => "true".fmt(f),
            False => "false".fmt(f),
            Uint8(uint) => write!(f, "{}u8", uint),
            Uint16(uint) => write!(f, "{}u16", uint),
            Uint32(uint) => write!(f, "{}u32", uint),
            Uint64(uint) => write!(f, "{}u64", uint),
            Uint128(uint) => write!(f, "{}u128", uint),
            UintSize(uint) => write!(f, "{}usize", uint),
            Int8(int) => write!(f, "{}i8", int),
            Int16(int) => write!(f, "{}i16", int),
            Int32(int) => write!(f, "{}i32", int),
            Int64(int) => write!(f, "{}i64", int),
            Int128(int) => write!(f, "{}i128", int),
            IntSize(int) => write!(f, "{}isize", int),
            Ident(symbol) => symbol.fmt(f),
            Fn => "fn".fmt(f),
            Add => "+".fmt(f),
            Sub => "-".fmt(f),
            Mul => "*".fmt(f),
            Div => "/".fmt(f),
            Rem => "%".fmt(f),
            And => "&&".fmt(f),
            Or => "||".fmt(f),
            Not => "!".fmt(f),
            Eq => "==".fmt(f),
            Neq => "!=".fmt(f),
            Gt => ">".fmt(f),
            Lt => "<".fmt(f),
            Gte => ">=".fmt(f),
            Lte => "<=".fmt(f),
            OpenParen => "(".fmt(f),
            CloseParen => ")".fmt(f),
            OpenBracket => "{{".fmt(f),
            CloseBracket => "}}".fmt(f),
            Pipe => "|".fmt(f),
            Colon => ";".fmt(f),
            Comma => ",".fmt(f),
            Arrow => "->".fmt(f),
            Invalid => "invalid character".fmt(f),
        }
    }
}
