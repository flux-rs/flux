use std::{collections::VecDeque, fmt, iter::Peekable};

pub use rustc_ast::token::{Delimiter, Lit, LitKind};
use rustc_ast::{
    token::{self, InvisibleOrigin, TokenKind},
    tokenstream::{TokenStream, TokenStreamIter, TokenTree},
};
use rustc_span::{BytePos, Symbol, symbol::kw};

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Token {
    Caret,
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
    Underscore,
    Fn,
    Async,
    Iff,
    FatArrow,
    Let,
    Mut,
    Where,
    Forall,
    Exists,
    In,
    Impl,
    Requires,
    Ensures,
    Literal(Lit),
    Ident(Symbol),
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    OpenBracket,
    CloseBracket,
    OpenInvisible(InvisibleOrigin),
    CloseInvisible(InvisibleOrigin),
    Invalid,
    Ref,
    And,
    Percent,
    Strg,
    Type,
    If,
    Else,
    PathSep,
    Qualifier,
    Sort,
    Opaque,
    Local,
    BitVec,
    As,
    Hrn,
    Hdl,
    DotDot,
    Eof,
}

impl Token {
    pub fn descr(&self) -> &'static str {
        match self {
            Token::Caret => "|",
            Token::EqEq => "==",
            Token::Eq => "=",
            Token::AndAnd => "&&",
            Token::OrOr => "||",
            Token::Plus => "+",
            Token::Minus => "-",
            Token::Slash => "/",
            Token::Bang => "!",
            Token::Star => "*",
            Token::Colon => ":",
            Token::Comma => ",",
            Token::Semi => ";",
            Token::RArrow => "->",
            Token::Dot => ".",
            Token::Le => "<=",
            Token::Ne => ">=",
            Token::GtFollowedByGt => ">",
            Token::Gt => ">",
            Token::LtFollowedByLt => "<",
            Token::Lt => "<",
            Token::Ge => ">=",
            Token::At => "@",
            Token::Pound => "#",
            Token::Underscore => "_",
            Token::Fn => "fn",
            Token::Async => "async",
            Token::Iff => "<=>",
            Token::FatArrow => "=>",
            Token::Let => "let",
            Token::Mut => "mut",
            Token::Where => "where",
            Token::Forall => "forall",
            Token::Exists => "exists",
            Token::In => "in",
            Token::Impl => "impl",
            Token::Requires => "requires",
            Token::Ensures => "ensures",
            Token::Literal(_) => "literal",
            Token::Ident(_) => "identifier",
            Token::OpenParen => "(",
            Token::OpenBrace => "{",
            Token::OpenBracket => "[",
            Token::CloseParen => ")",
            Token::CloseBrace => "}",
            Token::CloseBracket => "]",
            Token::OpenInvisible(_) => "",
            Token::CloseInvisible(_) => "",
            Token::Invalid => "<invalid>",
            Token::Ref => "ref",
            Token::And => "&",
            Token::Percent => "%",
            Token::Strg => "strg",
            Token::Type => "type",
            Token::If => "if",
            Token::Else => "else",
            Token::PathSep => "::",
            Token::Qualifier => "qualifier",
            Token::Sort => "sort",
            Token::Opaque => "opaque",
            Token::Local => "local",
            Token::BitVec => "bitvec",
            Token::As => "as",
            Token::Hrn => "rn",
            Token::Hdl => "hdl",
            Token::DotDot => "..",
            Token::Eof => "<eof>",
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Literal(lit) => write!(f, "{lit}"),
            Token::Ident(sym) => write!(f, "{sym}"),
            _ => write!(f, "{}", self.descr()),
        }
    }
}

pub struct Cursor<'t> {
    stack: Vec<Frame<'t>>,
    symbs: Symbols,
    tokens: VecDeque<(BytePos, Token, BytePos)>,
    hi: BytePos,
}

struct Symbols {
    requires: Symbol,
    ensures: Symbol,
    strg: Symbol,
    qualifier: Symbol,
    sort: Symbol,
    opaque: Symbol,
    local: Symbol,
    bitvec: Symbol,
    hrn: Symbol,
    hdl: Symbol,
    forall: Symbol,
    exists: Symbol,
}

struct Frame<'t> {
    cursor: Peekable<TokenStreamIter<'t>>,
    close: Option<(BytePos, Token, BytePos)>,
}

impl<'t> Cursor<'t> {
    pub(crate) fn new(stream: &'t TokenStream, offset: BytePos) -> Self {
        let mut cursor = Cursor {
            stack: vec![Frame { cursor: stream.iter().peekable(), close: None }],
            tokens: VecDeque::new(),
            symbs: Symbols {
                strg: Symbol::intern("strg"),
                requires: Symbol::intern("requires"),
                ensures: Symbol::intern("ensures"),
                qualifier: Symbol::intern("qualifier"),
                sort: Symbol::intern("sort"),
                bitvec: Symbol::intern("bitvec"),
                opaque: Symbol::intern("opaque"),
                local: Symbol::intern("local"),
                hrn: Symbol::intern("hrn"),
                hdl: Symbol::intern("hdl"),
                forall: Symbol::intern("forall"),
                exists: Symbol::intern("exists"),
            },
            hi: offset,
        };
        cursor.fetch_tokens();
        cursor
    }

    #[must_use]
    pub fn at(&mut self, pos: usize) -> (BytePos, Token, BytePos) {
        while self.tokens.len() <= pos && self.fetch_tokens() {}
        if pos < self.tokens.len() { self.tokens[pos] } else { (self.hi, Token::Eof, self.hi) }
    }

    pub fn debug(&mut self, size: usize) -> String {
        let mut s = String::new();
        for i in 0..size {
            s = format!("{s} {}", self.at(i).1);
        }
        s
    }

    pub fn advance(&mut self) {
        if let Some(tok) = self.tokens.pop_front() {
            if self.tokens.is_empty() {
                self.fetch_tokens();
            }
            self.hi = tok.2;
        }
    }

    pub fn advance_by(&mut self, n: usize) {
        for _ in 0..n {
            self.advance();
        }
    }

    /// Returns the starting byte position of the next token
    pub fn lo(&self) -> BytePos {
        if let Some((lo, ..)) = self.tokens.front() { *lo } else { self.hi }
    }

    /// Returns the highest byte position the cursor has yielded. You could also think of this as
    /// the ending position of the last yielded token.
    pub fn hi(&self) -> BytePos {
        self.hi
    }

    fn map_token(&mut self, token: &token::Token) {
        let span = token.span;
        let token = match token.kind {
            TokenKind::Lt => Token::Lt,
            TokenKind::Le => Token::Le,
            TokenKind::EqEq => Token::EqEq,
            TokenKind::Eq => Token::Eq,
            TokenKind::Ne => Token::Ne,
            TokenKind::AndAnd => Token::AndAnd,
            TokenKind::OrOr => Token::OrOr,
            TokenKind::FatArrow => Token::FatArrow,
            TokenKind::Gt => Token::Gt,
            TokenKind::Ge => Token::Ge,
            TokenKind::At => Token::At,
            TokenKind::Pound => Token::Pound,
            TokenKind::Comma => Token::Comma,
            TokenKind::Colon => Token::Colon,
            TokenKind::Semi => Token::Semi,
            TokenKind::RArrow => Token::RArrow,
            TokenKind::Dot => Token::Dot,
            TokenKind::OpenParen => Token::OpenParen,
            TokenKind::OpenBrace => Token::OpenBrace,
            TokenKind::OpenBracket => Token::OpenBracket,
            TokenKind::CloseParen => Token::CloseParen,
            TokenKind::CloseBrace => Token::CloseBrace,
            TokenKind::CloseBracket => Token::CloseBracket,

            TokenKind::Literal(lit) => Token::Literal(lit),
            TokenKind::Ident(symb, _) if symb == kw::True || symb == kw::False => {
                Token::Literal(Lit { kind: LitKind::Bool, symbol: symb, suffix: None })
            }
            TokenKind::Ident(symb, _) if symb == self.symbs.strg => Token::Strg,
            TokenKind::Ident(symb, _) if symb == self.symbs.requires => Token::Requires,
            TokenKind::Ident(symb, _) if symb == self.symbs.ensures => Token::Ensures,
            TokenKind::Ident(symb, _) if symb == self.symbs.qualifier => Token::Qualifier,
            TokenKind::Ident(symb, _) if symb == self.symbs.sort => Token::Sort,
            TokenKind::Ident(symb, _) if symb == self.symbs.opaque => Token::Opaque,
            TokenKind::Ident(symb, _) if symb == self.symbs.local => Token::Local,
            TokenKind::Ident(symb, _) if symb == self.symbs.bitvec => Token::BitVec,
            TokenKind::Ident(symb, _) if symb == self.symbs.hrn => Token::Hrn,
            TokenKind::Ident(symb, _) if symb == self.symbs.hdl => Token::Hdl,
            TokenKind::Ident(symb, _) if symb == self.symbs.forall => Token::Forall,
            TokenKind::Ident(symb, _) if symb == self.symbs.exists => Token::Exists,
            TokenKind::Ident(symb, _) if symb == kw::Let => Token::Let,
            TokenKind::Ident(symb, _) if symb == kw::In => Token::In,
            TokenKind::Ident(symb, _) if symb == kw::Ref => Token::Ref,
            TokenKind::Ident(symb, _) if symb == kw::Fn => Token::Fn,
            TokenKind::Ident(symb, _) if symb == kw::Mut => Token::Mut,
            TokenKind::Ident(symb, _) if symb == kw::Where => Token::Where,
            TokenKind::Ident(symb, _) if symb == kw::Impl => Token::Impl,
            TokenKind::Ident(symb, _) if symb == kw::Type => Token::Type,
            TokenKind::Ident(symb, _) if symb == kw::If => Token::If,
            TokenKind::Ident(symb, _) if symb == kw::Else => Token::Else,
            TokenKind::Ident(symb, _) if symb == kw::Async => Token::Async,
            TokenKind::Ident(symb, _) if symb == kw::As => Token::As,
            TokenKind::Ident(symb, _) if symb == kw::Underscore => Token::Underscore,
            TokenKind::Ident(symb, _) => Token::Ident(symb),
            TokenKind::Or => Token::Caret,
            TokenKind::Plus => Token::Plus,
            TokenKind::Slash => Token::Slash,
            TokenKind::Minus => Token::Minus,
            TokenKind::And => Token::And,
            TokenKind::Percent => Token::Percent,
            TokenKind::Star => Token::Star,
            TokenKind::Shl => {
                self.tokens
                    .push_back((span.lo(), Token::LtFollowedByLt, span.hi() - BytePos(1)));
                self.tokens
                    .push_back((span.lo() + BytePos(1), Token::Lt, span.hi()));
                return;
            }
            TokenKind::Shr => {
                self.tokens
                    .push_back((span.lo(), Token::GtFollowedByGt, span.hi() - BytePos(1)));
                self.tokens
                    .push_back((span.lo() + BytePos(1), Token::Gt, span.hi()));
                return;
            }
            TokenKind::Bang => Token::Bang,
            TokenKind::PathSep => Token::PathSep,
            TokenKind::DotDot => Token::DotDot,
            _ => Token::Invalid,
        };
        self.tokens.push_back((span.lo(), token, span.hi()));
    }

    fn fetch_tokens(&mut self) -> bool {
        let Some(top) = self.stack.last_mut() else { return false };

        match top.cursor.next() {
            Some(TokenTree::Token(token, _)) => {
                if let Some(TokenTree::Token(next, _)) = top.cursor.peek() {
                    match (&token.kind, &next.kind) {
                        (TokenKind::Le, TokenKind::Gt) if token.span.hi() == next.span.lo() => {
                            top.cursor.next();
                            self.tokens
                                .push_back((token.span.lo(), Token::Iff, next.span.hi()));
                            return true;
                        }
                        _ => {}
                    }
                }
                self.map_token(token);
                true
            }
            Some(TokenTree::Delimited(_, _spacing, Delimiter::Invisible(..), tokens)) => {
                self.stack
                    .push(Frame { cursor: tokens.iter().peekable(), close: None });
                self.fetch_tokens()
            }
            Some(TokenTree::Delimited(span, _spacing, delim, tokens)) => {
                let close_token = match delim {
                    Delimiter::Parenthesis => Token::CloseParen,
                    Delimiter::Brace => Token::CloseBrace,
                    Delimiter::Bracket => Token::CloseBracket,
                    Delimiter::Invisible(origin) => Token::CloseInvisible(*origin),
                };
                let close = (span.close.lo(), close_token, span.close.hi());

                self.stack
                    .push(Frame { cursor: tokens.iter().peekable(), close: Some(close) });

                let kind = match delim {
                    Delimiter::Parenthesis => TokenKind::OpenParen,
                    Delimiter::Brace => TokenKind::OpenBrace,
                    Delimiter::Bracket => TokenKind::OpenBracket,
                    Delimiter::Invisible(origin) => TokenKind::OpenInvisible(*origin),
                };

                let token = token::Token { kind, span: span.open };
                self.map_token(&token);
                true
            }
            None => {
                let Some(frame) = self.stack.pop() else { return false };
                if let Some(token) = frame.close {
                    self.tokens.push_back(token);
                    true
                } else {
                    self.fetch_tokens()
                }
            }
        }
    }
}
