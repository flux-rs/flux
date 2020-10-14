use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, char, digit1},
    combinator::{map, opt},
    multi::many0,
    sequence::{pair, preceded, separated_pair, terminated},
    IResult,
};

use crate::ty::{BaseTy, Expr, IntSize, Pred, RefinedTy, Variable};

fn parse_variable(input: &str) -> IResult<&str, Variable> {
    map(alpha1, |slice: &str| Variable(slice.to_owned()))(input)
}

fn parse_base_ty(input: &str) -> IResult<&str, BaseTy> {
    alt((
        map(preceded(char('u'), parse_int_base), BaseTy::Uint),
        map(preceded(char('i'), parse_int_base), BaseTy::Int),
    ))(input)
}

fn parse_int_base(input: &str) -> IResult<&str, IntSize> {
    alt((
        map(tag("8"), |_| IntSize::Size8),
        map(tag("16"), |_| IntSize::Size16),
        map(tag("32"), |_| IntSize::Size32),
        map(tag("64"), |_| IntSize::Size64),
        map(tag("128"), |_| IntSize::Size128),
        map(tag("size"), |_| IntSize::Unsized),
    ))(input)
}

fn parse_expr(input: &str) -> IResult<&str, Expr> {
    fn base(input: &str) -> IResult<&str, Expr> {
        alt((
            map(parse_const, Expr::Const),
            map(parse_variable, Expr::Var),
            terminated(preceded(char('('), parse_expr), char(')')),
        ))(input)
    }

    let (mut output, mut expr) = base(input)?;

    while let (new_output, Some((op, operand))) =
        opt(pair(alt((char('+'), char('-'), char('*'))), base))(output)?
    {
        expr = match op {
            '+' => Expr::Add(Box::new(expr), Box::new(operand)),
            '-' => Expr::Sub(Box::new(expr), Box::new(operand)),
            '*' => Expr::Mul(Box::new(expr), Box::new(operand)),
            _ => unreachable!(),
        };

        output = new_output;
    }

    Ok((output, expr))
}

fn parse_const(input: &str) -> IResult<&str, i128> {
    map(
        pair(opt(char('-')), digit1),
        |(sign, digits): (Option<char>, &str)| {
            let mut number = digits.parse::<i128>().unwrap();
            if sign.is_some() {
                number *= -1;
            }
            number
        },
    )(input)
}

fn parse_pred(input: &str) -> IResult<&str, Pred> {
    fn base(input: &str) -> IResult<&str, Pred> {
        alt((
            map(
                separated_pair(parse_expr, tag("=="), parse_expr),
                |(op1, op2)| Pred::Eq(op1, op2),
            ),
            map(
                separated_pair(parse_expr, char('<'), parse_expr),
                |(op1, op2)| Pred::Lt(op1, op2),
            ),
            map(preceded(char('!'), parse_pred), |pred| {
                Pred::Not(Box::new(pred))
            }),
            terminated(preceded(char('('), parse_pred), char(')')),
        ))(input)
    }

    let (mut output, mut pred) = base(input)?;

    while let (new_output, Some((op, operand))) =
        opt(pair(alt((tag("&&"), tag("||"))), base))(output)?
    {
        pred = match op {
            "&&" => Pred::And(Box::new(pred), Box::new(operand)),
            "||" => Pred::Or(Box::new(pred), Box::new(operand)),
            _ => unreachable!(),
        };

        output = new_output;
    }

    Ok((output, pred))
}

pub fn parse_ty(input: &str) -> IResult<&str, RefinedTy> {
    alt((
        map(parse_base_ty, RefinedTy::Base),
        map(
            terminated(
                preceded(
                    char('{'),
                    pair(
                        separated_pair(parse_variable, char(':'), parse_base_ty),
                        preceded(char('|'), parse_pred),
                    ),
                ),
                char('}'),
            ),
            |((var, ty), pred)| RefinedTy::RefBase(var, ty, pred),
        ),
        map(
            separated_pair(
                terminated(
                    preceded(
                        tag("fn("),
                        many0(separated_pair(parse_variable, char(':'), parse_ty)),
                    ),
                    char(')'),
                ),
                tag("->"),
                parse_ty,
            ),
            |(params, ret)| RefinedTy::RefFunc(params, Box::new(ret)),
        ),
    ))(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        dbg!(parse_ty("fn(x:usize)->{x:usize|0<x}"));
    }
}
