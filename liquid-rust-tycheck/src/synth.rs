use crate::{Env, GlobEnv, LocalVariable, Predicate, Ty, Variable};

use liquid_rust_common::{
    ir::{BinOp, Operand, Rvalue},
    ty::BaseTy,
};

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
            Operand::Literal(literal) => literal.as_singleton(),
        }
    }
}

impl Synth for Rvalue {
    fn synth(&self, genv: &GlobEnv, env: &mut Env) -> Ty {
        match self {
            Rvalue::Use(operand) => operand.synth(genv, env),
            Rvalue::UnApp(un_op, op) => {
                let base_ty = op
                    .synth(genv, env)
                    .get_base()
                    .expect("Operand has function type.");

                let op = env.resolve_operand(op);

                Ty::Refined(
                    base_ty,
                    Predicate::BinApp(
                        BinOp::Eq,
                        Box::new(Predicate::Var(Variable::Bounded)),
                        Box::new(Predicate::UnApp(*un_op, Box::new(op))),
                    ),
                )
            }
            Rvalue::BinApp(bin_op, op1, op2) => match bin_op {
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Lte | BinOp::Gte => {
                    let op1 = env.resolve_operand(op1);
                    let op2 = env.resolve_operand(op2);
                    Ty::Refined(
                        BaseTy::Bool,
                        Predicate::BinApp(
                            BinOp::Eq,
                            Box::new(Predicate::Var(Variable::Bounded)),
                            Box::new(Predicate::BinApp(*bin_op, Box::new(op1), Box::new(op2))),
                        ),
                    )
                }
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::And | BinOp::Or => {
                    let base_ty = op1
                        .synth(genv, env)
                        .get_base()
                        .expect("Operand has function type.");

                    let op1 = env.resolve_operand(op1);
                    let op2 = env.resolve_operand(op2);

                    Ty::Refined(
                        base_ty,
                        Predicate::BinApp(
                            BinOp::Eq,
                            Box::new(Predicate::Var(Variable::Bounded)),
                            Box::new(Predicate::BinApp(*bin_op, Box::new(op1), Box::new(op2))),
                        ),
                    )
                }
            },
        }
    }
}
