use crate::{
    env::Env,
    glob_env::GlobEnv,
    ty::{LocalVariable, Predicate, Ty, Variable},
};

use liquid_rust_mir::{Operand, Rvalue};
use liquid_rust_ty::{BaseTy, BinOp, UnOp};

pub(super) trait Synth {
    fn synth(&self, genv: &GlobEnv, env: &mut Env) -> Ty;
}

impl Synth for LocalVariable {
    fn synth(&self, _genv: &GlobEnv, env: &mut Env) -> Ty {
        env.get_ty(*self).clone()
    }
}

impl Synth for Operand {
    fn synth(&self, _genv: &GlobEnv, env: &mut Env) -> Ty {
        match self {
            // Syn-Var
            Operand::Local(local) => {
                let variable = env.resolve_local(*local);
                let ty = env.get_ty(variable).clone();
                ty.selfify(variable)
            }
            // Syn-Const
            Operand::Literal(literal) => Ty::singleton(*literal),
        }
    }
}

impl Synth for Rvalue {
    fn synth(&self, genv: &GlobEnv, env: &mut Env) -> Ty {
        match self {
            Rvalue::Use(operand) => operand.synth(genv, env),
            Rvalue::UnApp(un_op, op) => {
                let (op_ty, ret_ty) = match un_op {
                    UnOp::IntNot(sign, size) | UnOp::Neg(sign, size) => {
                        (BaseTy::Int(*sign, *size), BaseTy::Int(*sign, *size))
                    }
                    UnOp::Not => (BaseTy::Bool, BaseTy::Bool),
                };
                let op_ty1 = op.synth(genv, env);

                assert_eq!(op_ty1.get_base(), Some(op_ty));

                let op = env.resolve_operand(op);

                Ty::Refined(
                    ret_ty,
                    Predicate::BinApp(
                        BinOp::Eq(ret_ty),
                        Box::new(Predicate::Var(Variable::Bounded)),
                        Box::new(Predicate::UnApp(*un_op, Box::new(op))),
                    ),
                )
            }
            Rvalue::BinApp(bin_op, op1, op2) => {
                let (op_ty, ret_ty) = match bin_op {
                    BinOp::Add(sign, size)
                    | BinOp::Sub(sign, size)
                    | BinOp::Mul(sign, size)
                    | BinOp::Div(sign, size)
                    | BinOp::Rem(sign, size) => {
                        (BaseTy::Int(*sign, *size), BaseTy::Int(*sign, *size))
                    }
                    BinOp::And | BinOp::Or => (BaseTy::Bool, BaseTy::Bool),
                    BinOp::Eq(ty) | BinOp::Neq(ty) => (*ty, BaseTy::Bool),
                    BinOp::Lt(sign, size)
                    | BinOp::Gt(sign, size)
                    | BinOp::Lte(sign, size)
                    | BinOp::Gte(sign, size) => (BaseTy::Int(*sign, *size), BaseTy::Bool),
                };
                let op_ty1 = op1.synth(genv, env);
                let op_ty2 = op2.synth(genv, env);

                assert!(op_ty1.shape_eq(&op_ty2));
                assert_eq!(op_ty1.get_base(), Some(op_ty));

                let op1 = env.resolve_operand(op1);
                let op2 = env.resolve_operand(op2);

                Ty::Refined(
                    ret_ty,
                    Predicate::BinApp(
                        BinOp::Eq(ret_ty),
                        Box::new(Predicate::Var(Variable::Bounded)),
                        Box::new(Predicate::BinApp(*bin_op, Box::new(op1), Box::new(op2))),
                    ),
                )
            }
        }
    }
}
