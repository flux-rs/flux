use liquid_rust_core::{
    ast,
    ty::{self, Ty, TyCtxt},
};

use crate::env::Env;

pub trait Synth {
    fn synth(&self, tcx: &TyCtxt, env: &mut Env) -> Ty;
}

impl Synth for ast::Rvalue {
    fn synth(&self, tcx: &TyCtxt, env: &mut Env) -> Ty {
        match self {
            ast::Rvalue::Use(op) => op.synth(tcx, env),
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
                    let ty = op.synth(tcx, env);
                    assert!(ty.is_bool());
                    tcx.types.bool()
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
    let ty1 = op1.synth(tcx, env);
    let ty2 = op2.synth(tcx, env);
    let bty = match bin_op {
        ast::BinOp::Add | ast::BinOp::Sub => {
            assert!(ty1.is_int());
            assert!(ty2.is_int());
            ty::BaseType::Int
        }
        ast::BinOp::Eq => {
            assert!(ty1.shape_eq(&ty2));
            ty::BaseType::Bool
        }
        ast::BinOp::Lt | ast::BinOp::Le | ast::BinOp::Ge | ast::BinOp::Gt => {
            assert!(ty1.is_int());
            assert!(ty2.is_int());
            ty::BaseType::Bool
        }
    };
    tcx.mk_unrefined(bty)
}

impl Synth for ast::Operand {
    fn synth(&self, cx: &TyCtxt, env: &mut Env) -> Ty {
        match self {
            ast::Operand::Use(place) => env.lookup(place).clone(),
            ast::Operand::Constant(c) => c.synth(cx, env),
        }
    }
}

impl Synth for ast::Constant {
    fn synth(&self, tcx: &TyCtxt, _env: &mut Env) -> Ty {
        match self {
            ast::Constant::Bool(_) => tcx.types.bool(),
            ast::Constant::Int(_) => tcx.types.int(),
            ast::Constant::Unit => tcx.types.unit(),
        }
    }
}
