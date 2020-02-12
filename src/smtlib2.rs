extern crate rsmt2;
extern crate rustc_apfloat;
extern crate syntax as rust_syntax;

use super::refinements::{Place, Pred, Scalar, Var};
use super::syntax::ast::{BinOpKind, UnOpKind};
pub use rsmt2::errors::SmtRes;
pub use rsmt2::print::{Expr2Smt, Sym2Smt};
pub use rsmt2::Solver;
use rust_syntax::ast::FloatTy;
use rustc::mir;
use rustc::mir::interpret::sign_extend;
use rustc::ty::layout::Size;
use rustc::ty::{self, Ty};
use rustc_apfloat::{
    ieee::{Double, Single},
    Float,
};
use std::io::Write;

enum Token<'a, 'tcx> {
    Expr(&'a Pred<'a, 'tcx>),
    Space,
    Paren,
}

impl Expr2Smt<()> for Pred<'_, '_> {
    fn expr_to_smt2<Writer: Write>(&self, w: &mut Writer, info: ()) -> SmtRes<()> {
        let mut stack = vec![Token::Expr(self)];
        while let Some(token) = stack.pop() {
            match token {
                Token::Expr(Pred::Place(place)) => place.sym_to_smt2(w, info)?,
                Token::Expr(Pred::Constant(ty, scalar)) => format_scalar(ty, *scalar, w)?,
                Token::Expr(Pred::Binary(lhs, op, rhs)) => {
                    write!(w, "({} ", bin_op_to_smt2(*op))?;
                    stack.push(Token::Paren);
                    stack.push(Token::Expr(rhs));
                    stack.push(Token::Space);
                    stack.push(Token::Expr(lhs));
                }
                Token::Expr(Pred::Unary(UnOpKind::Not, expr)) => {
                    write!(w, "(not ")?;
                    stack.push(Token::Paren);
                    stack.push(Token::Expr(expr));
                }
                Token::Expr(Pred::Unary(UnOpKind::Deref, _)) => unimplemented!(),
                Token::Space => write!(w, " ")?,
                Token::Paren => write!(w, ")")?,
            }
        }
        Ok(())
    }
}

impl Pred<'_, '_> {
    pub fn to_smt_str(&self) -> String {
        let mut v = Vec::new();
        match self.expr_to_smt2(&mut v, ()) {
            Ok(_) => String::from_utf8(v).unwrap_or("error".into()),
            Err(_) => "error".into(),
        }
    }
}

impl Sym2Smt<()> for Place<'_> {
    fn sym_to_smt2<Writer: Write>(&self, w: &mut Writer, _info: ()) -> SmtRes<()> {
        match self.var {
            Var::Local(local) => write!(w, "_{}", local.index())?,
            Var::Free(idx) => write!(w, "${}", idx)?,
            Var::Bound(_) => bug!("place has a bound variable: {:?}", self),
        }
        for elem in self.projection.iter() {
            match elem {
                mir::ProjectionElem::Field(field, _) => {
                    write!(w, ".{}", field.index())?;
                }
                _ => unimplemented!(),
            }
        }
        Ok(())
    }
}

fn format_scalar<'tcx, W: Write>(ty: Ty<'tcx>, scalar: Scalar, w: &mut W) -> SmtRes<()> {
    match &ty.kind {
        ty::Bool => write!(w, "{}", if scalar.data == 0 { "false" } else { "true" })?,
        ty::Float(FloatTy::F32) => write!(w, "{}", Single::from_bits(scalar.data))?,
        ty::Float(FloatTy::F64) => write!(w, "{}", Double::from_bits(scalar.data))?,
        ty::Uint(_) => {
            write!(w, "{}", scalar.data)?;
        }
        ty::Int(i) => {
            // TODO: assuming 64 bits for isize. we can probably make this configurable
            let bit_width = i.bit_width().unwrap_or(64) as u64;
            let size = Size::from_bits(bit_width);
            write!(w, "{}", sign_extend(scalar.data, size) as i128)?;
        }
        _ => bug!(),
    }
    Ok(())
}

fn bin_op_to_smt2(op: BinOpKind) -> &'static str {
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
