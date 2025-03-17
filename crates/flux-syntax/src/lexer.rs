use std::{collections::VecDeque, fmt, iter::Peekable};

pub use rustc_ast::token::{BinOpToken, Delimiter, Lit, LitKind};
use rustc_ast::{
    token::{self, TokenKind},
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
    Not,
    Star,
    Shl,
    Colon,
    Comma,
    Semi,
    RArrow,
    Dot,
    Lt,
    Le,
    Ne,
    Gt,
    GtFollowedByGt,
    Ge,
    At,
    Pound,
    Underscore,
    Fn,
    Async,
    Iff,
    FatArrow,
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
    OpenDelim(Delimiter),
    CloseDelim(Delimiter),
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

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Caret => write!(f, "|"),
            Token::EqEq => write!(f, "=="),
            Token::Eq => write!(f, "="),
            Token::AndAnd => write!(f, "&&"),
            Token::OrOr => write!(f, "||"),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Slash => write!(f, "/"),
            Token::Not => write!(f, "!"),
            Token::Star => write!(f, "*"),
            Token::Shl => write!(f, "<<"),
            Token::Colon => write!(f, ":"),
            Token::Comma => write!(f, ","),
            Token::Semi => write!(f, ";"),
            Token::RArrow => write!(f, "->"),
            Token::Dot => write!(f, "."),
            Token::Lt => write!(f, "<"),
            Token::Le => write!(f, "<="),
            Token::Ne => write!(f, ">="),
            Token::Gt => write!(f, ">"),
            Token::GtFollowedByGt => write!(f, ">"),
            Token::Ge => write!(f, ">="),
            Token::At => write!(f, "@"),
            Token::Pound => write!(f, "#"),
            Token::Underscore => write!(f, "_"),
            Token::Fn => write!(f, "fn"),
            Token::Async => write!(f, "async"),
            Token::Iff => write!(f, "<=>"),
            Token::FatArrow => write!(f, "=>"),
            Token::Mut => write!(f, "mut"),
            Token::Where => write!(f, "where"),
            Token::Forall => write!(f, "forall"),
            Token::Exists => write!(f, "exists"),
            Token::In => write!(f, "in"),
            Token::Impl => write!(f, "impl"),
            Token::Requires => write!(f, "requires"),
            Token::Ensures => write!(f, "ensures"),
            Token::Literal(lit) => write!(f, "{lit}"),
            Token::Ident(sym) => write!(f, "{sym}"),
            Token::OpenDelim(Delimiter::Parenthesis) => write!(f, "("),
            Token::OpenDelim(Delimiter::Brace) => write!(f, "{{"),
            Token::OpenDelim(Delimiter::Bracket) => write!(f, "["),
            Token::OpenDelim(Delimiter::Invisible(_)) => write!(f, ""),
            Token::CloseDelim(Delimiter::Parenthesis) => write!(f, ")"),
            Token::CloseDelim(Delimiter::Brace) => write!(f, "}}"),
            Token::CloseDelim(Delimiter::Bracket) => write!(f, "]"),
            Token::CloseDelim(Delimiter::Invisible(_)) => write!(f, ""),
            Token::Invalid => write!(f, "<invalid>"),
            Token::Ref => write!(f, "ref"),
            Token::And => write!(f, "&"),
            Token::Percent => write!(f, "%"),
            Token::Strg => write!(f, "strg"),
            Token::Type => write!(f, "type"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::PathSep => write!(f, "::"),
            Token::Qualifier => write!(f, "qualifier"),
            Token::Sort => write!(f, "sort"),
            Token::Opaque => write!(f, "opaque"),
            Token::Local => write!(f, "local"),
            Token::BitVec => write!(f, "bitvec"),
            Token::As => write!(f, "as"),
            Token::Hrn => write!(f, "rn"),
            Token::Hdl => write!(f, "hdl"),
            Token::DotDot => write!(f, ".."),
            Token::Eof => write!(f, "<eof>"),
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
    pub fn at(&mut self, pos: usize) -> Token {
        while self.tokens.len() <= pos && self.fetch_tokens() {}
        if pos < self.tokens.len() { self.tokens[pos].1 } else { Token::Eof }
    }

    pub fn debug(&mut self, size: usize) -> String {
        let mut s = String::new();
        for i in 0..size {
            s = format!("{s} {}", self.at(i));
        }
        s
    }

    #[must_use]
    pub fn next(&mut self) -> Token {
        if let Some(tok) = self.tokens.pop_front() {
            if self.tokens.is_empty() {
                self.fetch_tokens();
            }
            self.hi = tok.2;
            tok.1
        } else {
            Token::Eof
        }
    }

    pub fn advance_by(&mut self, n: usize) {
        for _ in 0..n {
            let _ = self.next();
        }
    }

    pub fn lo(&self) -> BytePos {
        if let Some((lo, ..)) = self.tokens.front() { *lo } else { self.hi }
    }

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
            TokenKind::OpenDelim(delim) => Token::OpenDelim(delim),
            TokenKind::CloseDelim(delim) => Token::CloseDelim(delim),
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
            TokenKind::BinOp(BinOpToken::Or) => Token::Caret,
            TokenKind::BinOp(BinOpToken::Plus) => Token::Plus,
            TokenKind::BinOp(BinOpToken::Slash) => Token::Slash,
            TokenKind::BinOp(BinOpToken::Minus) => Token::Minus,
            TokenKind::BinOp(BinOpToken::And) => Token::And,
            TokenKind::BinOp(BinOpToken::Percent) => Token::Percent,
            TokenKind::BinOp(BinOpToken::Star) => Token::Star,
            TokenKind::BinOp(BinOpToken::Shl) => Token::Shl,
            TokenKind::BinOp(BinOpToken::Shr) => {
                self.push_token(span.lo(), Token::GtFollowedByGt, span.hi() - BytePos(1));
                self.push_token(span.lo() + BytePos(1), Token::Gt, span.hi());
                return;
            }
            TokenKind::Not => Token::Not,
            TokenKind::PathSep => Token::PathSep,
            TokenKind::DotDot => Token::DotDot,
            _ => Token::Invalid,
        };
        self.push_token(span.lo(), token, span.hi());
    }

    fn push_token(&mut self, lo: BytePos, token: Token, hi: BytePos) {
        self.tokens.push_back((lo, token, hi));
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
                let close = (span.close.lo(), Token::CloseDelim(*delim), span.close.hi());

                self.stack
                    .push(Frame { cursor: tokens.iter().peekable(), close: Some(close) });

                let token = token::Token { kind: TokenKind::OpenDelim(*delim), span: span.open };
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
