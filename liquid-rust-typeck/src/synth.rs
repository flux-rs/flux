use liquid_rust_core::{
    ast,
    ty::{self, Ty, TyCtxt},
};
use ty::BaseTy;

use crate::env::Env;

pub trait Synth {
    fn synth(&self, tcx: &TyCtxt, env: &mut Env) -> Ty;
}

impl Synth for ast::Rvalue {
    fn synth(&self, tcx: &TyCtxt, env: &mut Env) -> Ty {
        match self {
            ast::Rvalue::Use(op @ ast::Operand::Constant(c)) => {
                let pred = env.resolve_operand(op);
                tcx.mk_refine(
                    c.base_ty(),
                    tcx.mk_bin_op(ty::BinOp::Eq, tcx.preds.nu(), pred),
                )
            }
            ast::Rvalue::Use(ast::Operand::Use(place)) => {
                let ty = env.lookup(place);
                tcx.selfify(ty, env.resolve_place(place))
            }
            ast::Rvalue::Ref(bk, place) => {
                let l = env.borrow(place);
                tcx.mk_ref(*bk, ty::Region::from(place.clone()), l)
            }
            ast::Rvalue::BinaryOp(bin_op, op1, op2) => synth_bin_op(tcx, env, bin_op, op1, op2),
            ast::Rvalue::CheckedBinaryOp(bin_op, op1, op2) => {
                let ty = synth_bin_op(tcx, env, bin_op, op1, op2);
                let f1 = tcx.fresh_field();
                let f2 = tcx.fresh_field();
                tcx.mk_tuple(tup!(f1 => ty, f2 => tcx.types.bool()))
            }
            ast::Rvalue::UnaryOp(un_op, op) => match un_op {
                ast::UnOp::Not => {
                    let pred = env.resolve_operand(op);
                    tcx.mk_refine(BaseTy::Bool, pred)
                }
            },
        }
    }
}

fn synth_bin_op(
    tcx: &TyCtxt,
    env: &mut Env,
    bin_op: &ast::BinOp,
    op1: &ast::Operand,
    op2: &ast::Operand,
) -> Ty {
    use ast::BinOp as ast;
    use ty::BinOp::*;
    let op1 = env.resolve_operand(op1);
    let op2 = env.resolve_operand(op2);
    let (bty, pred) = match bin_op {
        ast::Add => (
            BaseTy::Int,
            tcx.mk_bin_op(Eq, tcx.preds.nu(), tcx.mk_bin_op(Add, op1, op2)),
        ),
        ast::Sub => (
            BaseTy::Int,
            tcx.mk_bin_op(Eq, tcx.preds.nu(), tcx.mk_bin_op(Sub, op1, op2)),
        ),
        ast::Eq => (
            BaseTy::Bool,
            tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Eq, op1, op2)),
        ),
        ast::Lt => (
            BaseTy::Bool,
            tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Lt, op1, op2)),
        ),
        ast::Le => (
            BaseTy::Bool,
            tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Le, op1, op2)),
        ),
        ast::Ge => (
            BaseTy::Bool,
            tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Ge, op1, op2)),
        ),
        ast::Gt => (
            BaseTy::Bool,
            tcx.mk_bin_op(Iff, tcx.preds.nu(), tcx.mk_bin_op(Gt, op1, op2)),
        ),
    };
    tcx.mk_refine(bty, pred)
}
