use logos::Logos;
use std::fmt;

/// Tokens for the liquid rust's AST.
#[derive(Logos, Debug, Clone)]
pub enum Token<'source> {
    /// The `bool` token.
    #[token("bool")]
    Bool,
    /// The `int` token.
    #[token("int")]
    Int,
    /// The `true` token.
    #[token("true")]
    True,
    /// The `false` token.
    #[token("false")]
    False,
    /// An unsigned integer token.
    #[regex("[0-9]+", |lex| lex.slice().parse())]
    Integer(u128),
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
    /// The `.` token.
    #[token(".")]
    Dot,
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
            Int => "int".fmt(f),
            True => "true".fmt(f),
            False => "false".fmt(f),
            Integer(int) => write!(f, "{}", int),
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
            Dot => ".".fmt(f),
            Arrow => "->".fmt(f),
            Invalid => "invalid character".fmt(f),
        }
    }
}
