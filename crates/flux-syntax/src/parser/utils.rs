use super::{LAngle, Peek, RAngle};
use crate::{
    ParseCtxt, ParseResult,
    lexer::{Delimiter, Token},
};

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

pub(crate) fn brackets<R>(
    cx: &mut ParseCtxt,
    sep: Token,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    Ok(punctuated(cx, Delimiter::Bracket, sep, parse)?.0)
}

pub(crate) fn parens<R>(
    cx: &mut ParseCtxt,
    sep: Token,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    Ok(punctuated(cx, Delimiter::Parenthesis, sep, parse)?.0)
}

pub(crate) fn braces<R>(
    cx: &mut ParseCtxt,
    sep: Token,
    parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    Ok(punctuated(cx, Delimiter::Brace, sep, parse)?.0)
}

/// Parses a list of zero or more items surrounded by a delimiter and separated by a punctuation,
/// with optional trailing punctuation. Parsing continues until the requested closing delimiter
/// is reached. This consume the closing delimiter.
pub(crate) fn punctuated<R>(
    cx: &mut ParseCtxt,
    delim: Delimiter,
    sep: Token,
    mut parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<(Vec<R>, bool)> {
    cx.expect(Token::OpenDelim(delim))?;
    let mut items = vec![];

    let mut trailing = false;
    while !cx.peek(Token::CloseDelim(delim)) {
        items.push(parse(cx)?);

        trailing = cx.advance_if(sep);
        if !trailing {
            break;
        }
    }
    cx.expect(Token::CloseDelim(delim))?;
    Ok((items, trailing))
}

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
pub(crate) fn until<P: Peek + Copy, R>(
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
pub(crate) fn punctuated_until<E: Peek + Copy, R>(
    cx: &mut ParseCtxt,
    sep: Token,
    end: E,
    mut parse: impl FnMut(&mut ParseCtxt) -> ParseResult<R>,
) -> ParseResult<Vec<R>> {
    let mut items = vec![];
    while !cx.peek(end) {
        items.push(parse(cx)?);
        if !cx.advance_if(sep) {
            break;
        }
    }
    Ok(items)
}
