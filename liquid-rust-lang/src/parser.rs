use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, char, digit1, space0},
    combinator::{map, opt},
    multi::separated_list0,
    sequence::{pair, preceded, separated_pair, terminated, tuple},
    IResult,
};

use crate::{
    ast::{Predicate, Ty, Variable},
    ir::{BinOp, Literal, UnOp},
    ty::{BaseTy, IntSize},
};

fn symbol(string: &'static str) -> impl Fn(&str) -> IResult<&str, &str> {
    move |input| {
        map(tuple((space0, tag(string), space0)), |(_, output, _)| {
            output
        })(input)
    }
}

fn variable(input: &str) -> IResult<&str, Variable> {
    map(alpha1, |slice: &str| Variable(slice.to_owned()))(input)
}

fn integer(input: &str) -> IResult<&str, u128> {
    map(digit1, |digits: &str| digits.parse::<u128>().unwrap())(input)
}

fn literal(input: &str) -> IResult<&str, Literal> {
    alt((
        map(symbol("true"), |_| Literal::Bool(true)),
        map(symbol("false"), |_| Literal::Bool(false)),
        map(
            separated_pair(integer, symbol("_u"), int_size),
            |(int, size)| Literal::Uint(int, size),
        ),
        map(
            separated_pair(integer, symbol("_i"), int_size),
            |(int, size)| Literal::Int(int as i128, size),
        ),
    ))(input)
}

fn base_ty(input: &str) -> IResult<&str, BaseTy> {
    alt((
        map(preceded(char('u'), int_size), BaseTy::Uint),
        map(preceded(char('i'), int_size), BaseTy::Int),
        map(symbol("bool"), |_| BaseTy::Bool),
    ))(input)
}

fn int_size(input: &str) -> IResult<&str, IntSize> {
    alt((
        map(symbol("8"), |_| IntSize::Size8),
        map(symbol("16"), |_| IntSize::Size16),
        map(symbol("32"), |_| IntSize::Size32),
        map(symbol("64"), |_| IntSize::Size64),
        map(symbol("128"), |_| IntSize::Size128),
        map(symbol("size"), |_| IntSize::SizePtr),
    ))(input)
}

fn bin_app<'a>(
    bin_op: impl FnMut(&'a str) -> IResult<&'a str, BinOp>,
    mut op: impl FnMut(&'a str) -> IResult<&'a str, Predicate>,
    input: &'a str,
) -> IResult<&'a str, Predicate> {
    let (mut input, mut pred) = op(input)?;

    let mut app = opt(pair(bin_op, op));

    while let (output, Some((op, tail))) = app(input)? {
        pred = Predicate::BinApp(op, Box::new(pred), Box::new(tail));
        input = output;
    }

    Ok((input, pred))
}

fn un_op(input: &str) -> IResult<&str, UnOp> {
    alt((
        map(symbol("!"), |_| UnOp::Not),
        map(symbol("-"), |_| UnOp::Neg),
    ))(input)
}

fn predicate(input: &str) -> IResult<&str, Predicate> {
    let base_pred = |input| {
        alt((
            map(variable, Predicate::Var),
            map(literal, Predicate::Lit),
            map(pair(un_op, predicate), |(op, pred)| {
                Predicate::UnApp(op, Box::new(pred))
            }),
            map(
                tuple((symbol("("), predicate, symbol(")"))),
                |(_, pred, _)| pred,
            ),
        ))(input)
    };

    let bin_app_5 = |input| bin_app(map(symbol("*"), |_| BinOp::Mul), base_pred, input);

    let bin_app_4 = |input| {
        bin_app(
            alt((
                map(symbol("+"), |_| BinOp::Add),
                map(symbol("-"), |_| BinOp::Sub),
            )),
            bin_app_5,
            input,
        )
    };

    let bin_app_3 = |input| {
        bin_app(
            alt((
                map(symbol("=="), |_| BinOp::Eq),
                map(symbol("!="), |_| BinOp::Neq),
                map(symbol(">="), |_| BinOp::Gte),
                map(symbol("<="), |_| BinOp::Lte),
                map(symbol(">"), |_| BinOp::Gt),
                map(symbol("<"), |_| BinOp::Lt),
            )),
            bin_app_4,
            input,
        )
    };

    let bin_app_2 = |input| bin_app(map(symbol("&&"), |_| BinOp::And), bin_app_3, input);

    let bin_app_1 = |input| bin_app(map(symbol("||"), |_| BinOp::Or), bin_app_2, input);

    bin_app_1(input)
}

pub fn parse_ty(input: &str) -> IResult<&str, Ty> {
    alt((
        map(base_ty, Ty::Base),
        map(
            terminated(
                preceded(
                    symbol("{"),
                    pair(
                        separated_pair(variable, symbol(":"), base_ty),
                        preceded(symbol("|"), predicate),
                    ),
                ),
                symbol("}"),
            ),
            |((var, ty), pred)| Ty::RefBase(var, ty, pred),
        ),
        map(
            separated_pair(
                terminated(
                    preceded(
                        pair(symbol("fn"), symbol("(")),
                        separated_list0(symbol(","), separated_pair(variable, symbol(":"), parse_ty)),
                    ),
                    symbol(")"),
                ),
                symbol("->"),
                parse_ty,
            ),
            |(params, ret)| Ty::RefFunc(params, Box::new(ret)),
        ),
    ))(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        dbg!(
            parse_ty("fn(x: usize) -> { x: usize | x * 1_usize + 0_usize > 0_usize + 1_usize }")
                .unwrap()
        );
    }
}
