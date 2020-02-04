extern crate rsmt2;
extern crate rustc_apfloat;
extern crate syntax as rust_syntax;

use super::refinements::Refine;
use super::syntax::ast::BinOpKind;
pub use rsmt2::errors::SmtRes;
pub use rsmt2::print::Expr2Smt;
pub use rsmt2::Solver;
use rust_syntax::ast::FloatTy;
use rustc::mir;
use rustc::mir::interpret::{sign_extend, ConstValue, Scalar};
use rustc::ty::layout::Size;
use rustc::ty::{self, Ty};
use rustc_apfloat::{
    ieee::{Double, Single},
    Float,
};
use std::io::Write;

#[derive(Copy, Clone)]
pub struct SmtInfo {
    pub nu: mir::Local,
}

enum Token<'rcx, 'tcx> {
    CloseParen,
    Expr(&'rcx Refine<'rcx, 'tcx>),
    Space,
}

impl<'rcx, 'tcx> Expr2Smt<SmtInfo> for Refine<'rcx, 'tcx> {
    fn expr_to_smt2<Writer: Write>(&self, w: &mut Writer, info: SmtInfo) -> SmtRes<()> {
        let mut stack = vec![Token::Expr(self)];
        while let Some(token) = stack.pop() {
            match token {
                Token::CloseParen => write!(w, ")")?,
                Token::Space => write!(w, " ")?,
                Token::Expr(Refine::Nu) => write!(w, "{:?}", info.nu)?,
                Token::Expr(Refine::Place(place)) => write!(w, "{:?}", place)?,
                Token::Expr(Refine::Constant(ty, val)) => format_const_value(ty, *val, w)?,
                Token::Expr(Refine::Binary(lhs, op, rhs)) => {
                    write!(w, "({} ", bin_op_to_smt2(op))?;
                    stack.push(Token::CloseParen);
                    stack.push(Token::Expr(rhs));
                    stack.push(Token::Space);
                    stack.push(Token::Expr(lhs));
                }
                // TODO: Consider other unary operators
                Token::Expr(Refine::Unary(_op, expr)) => {
                    write!(w, "(not ")?;
                    stack.push(Token::CloseParen);
                    stack.push(Token::Expr(expr));
                }
            };
        }
        Ok(())
    }
}

fn format_const_value<'tcx, W: Write>(
    ty: Ty<'tcx>,
    val: ConstValue<'tcx>,
    w: &mut W,
) -> SmtRes<()> {
    match (val, &ty.kind) {
        (ConstValue::Scalar(Scalar::Raw { data, .. }), ty::Bool) => {
            write!(w, "{}", if data == 0 { "false" } else { "true" })?
        }
        (ConstValue::Scalar(Scalar::Raw { data, .. }), ty::Float(FloatTy::F32)) => {
            write!(w, "{}", Single::from_bits(data))?
        }
        (ConstValue::Scalar(Scalar::Raw { data, .. }), ty::Float(FloatTy::F64)) => {
            write!(w, "{}", Double::from_bits(data))?
        }
        (ConstValue::Scalar(Scalar::Raw { data, .. }), ty::Uint(_)) => {
            write!(w, "{}", data)?;
        }
        (ConstValue::Scalar(Scalar::Raw { data, .. }), ty::Int(i)) => {
            // TODO: assuming 64 bits for isize. we can make this configurable
            let bit_width = i.bit_width().unwrap_or(64) as u64;
            let size = Size::from_bits(bit_width);
            write!(w, "{}", sign_extend(data, size) as i128)?;
        }
        _ => unimplemented!(),
    }
    Ok(())
}

fn bin_op_to_smt2(op: &BinOpKind) -> &'static str {
    match op {
        BinOpKind::And => "and",
        BinOpKind::Or => "or",

        BinOpKind::Eq => "=",
        BinOpKind::Lt => "<",
        BinOpKind::Gt => ">",
        BinOpKind::Ge => ">=",

        BinOpKind::Mul => "*",
        BinOpKind::Div => "/",
        BinOpKind::Add => "+",
        BinOpKind::Sub => "-",
    }
}
