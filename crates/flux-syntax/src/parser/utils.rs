//! Implementation of parser combinators

use super::{LAngle, RAngle, lookahead::Peek};
use crate::{
    ParseCtxt, ParseResult,
    lexer::{Delimiter, Token},
};

/// Parses a list of one ore more items separated by the requested token. Parsing continues
/// until no separation token is found.
pub(crate) fn sep1<R>(
    cx: &mut ParseCtxt,
    sep: Token,
    mut parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    let mut items = vec![parse(cx)?];
    while cx.advance_if(sep) {
        items.push(parse(cx)?);
    }
    Ok(items)
}

/// Parses a list of zero or more items. Parsing continues until the requested `end` token
/// is reached. This does not consume the end token.
pub(crate) fn until<P: Peek, R>(
    cx: &mut ParseCtxt,
    end: P,
    mut parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    let mut items = vec![];
    while !cx.peek(end) {
        items.push(parse(cx)?);
    }
    Ok(items)
}

/// Parses a list of zero or more items separated by a punctuation, with optional trailing
/// punctuation. Parsing continues until the requested `end` token is reached. This does not
/// consume the end token.
///
/// Returns the vector of items and a boolean indicating whether trailing punctuation was present.
pub(crate) fn punctuated_with_trailing<E: Peek, R>(
    cx: &mut ParseCtxt,
    sep: Token,
    end: E,
    mut parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<(Vec<R>, bool)> {
    let mut items = vec![];
    let mut trailing = false;
    while !cx.peek(end) {
        items.push(parse(cx)?);
        trailing = cx.advance_if(sep);
        if !trailing {
            break;
        }
    }
    Ok((items, trailing))
}

/// Parses a list of zero or more items separated by a punctuation, with optional trailing
/// punctuation. Parsing continues until the requested `end` token is reached. This does not
/// consume the end token.
pub(crate) fn punctuated_until<E: Peek, R>(
    cx: &mut ParseCtxt,
    sep: Token,
    end: E,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    Ok(punctuated_with_trailing(cx, sep, end, parse)?.0)
}

/// Parses an item surrounded by an opening an closing [`Delimiter`]
pub(crate) fn delimited<R>(
    cx: &mut ParseCtxt,
    delim: Delimiter,
    parse: impl FnOnce(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<R> {
    cx.expect(Token::OpenDelim(delim))?;
    let r = parse(cx)?;
    cx.expect(Token::CloseDelim(delim))?;
    Ok(r)
}

pub(crate) fn opt_angle<R>(
    cx: &mut ParseCtxt,
    sep: Token,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    if !cx.peek(LAngle) {
        return Ok(vec![]);
    }
    angle(cx, sep, parse)
}

pub(crate) fn angle<R>(
    cx: &mut ParseCtxt,
    sep: Token,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    cx.expect(LAngle)?;
    let items = punctuated_until(cx, sep, RAngle, parse)?;
    cx.expect(RAngle)?;
    Ok(items)
}

fn punctuated_delimited<R>(
    cx: &mut ParseCtxt,
    delim: Delimiter,
    sep: Token,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    cx.expect(Token::OpenDelim(delim))?;
    let r = punctuated_until(cx, sep, Token::CloseDelim(delim), parse)?;
    cx.expect(Token::CloseDelim(delim))?;
    Ok(r)
}

pub(crate) fn brackets<R>(
    cx: &mut ParseCtxt,
    sep: Token,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    punctuated_delimited(cx, Delimiter::Bracket, sep, parse)
}

pub(crate) fn parens<R>(
    cx: &mut ParseCtxt,
    sep: Token,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    punctuated_delimited(cx, Delimiter::Parenthesis, sep, parse)
}

pub(crate) fn braces<R>(
    cx: &mut ParseCtxt,
    sep: Token,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    punctuated_delimited(cx, Delimiter::Brace, sep, parse)
}
