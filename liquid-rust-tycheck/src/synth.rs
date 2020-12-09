use crate::{env::Env, glob_env::GlobEnv};

use liquid_rust_mir::{Operand, Rvalue};
use liquid_rust_ty::{BaseTy, BinOp, LocalVariable, Predicate, Ty, UnOp, Variable};

/// Rule to synthetize a type for a term.
pub trait Synth<S> {
    fn synth(&self, genv: &GlobEnv<S>, env: &mut Env<S>) -> Ty;
}

impl<S> Synth<S> for LocalVariable {
    // This returns the type of a local variable without selfification. Most likely you want to use
    // the synth rule for operands. This rule only exists to synthetize the return type.
    fn synth(&self, _genv: &GlobEnv<S>, env: &mut Env<S>) -> Ty {
        env.get_ty(*self).clone()
    }
}

impl<S> Synth<S> for Operand {
    fn synth(&self, _genv: &GlobEnv<S>, env: &mut Env<S>) -> Ty {
        match self {
            // Follow the `Syn-Var` rule.
            Operand::Local(local) => {
                let variable = env.resolve_local(*local);
                // The type of the local is the type stored in the environment after selfification
                env.get_ty(variable).clone().selfify(variable)
            }
            // Follow the `Syn-Const` rule.
            Operand::Literal(literal) => {
                // the type of a literal is the singleton type for the literal.
                Ty::singleton(*literal)
            }
        }
    }
}

impl<S> Synth<S> for Rvalue {
    fn synth(&self, genv: &GlobEnv<S>, env: &mut Env<S>) -> Ty {
        match self {
            // Using an operand has the type of the operand.
            Rvalue::Use(operand) => operand.synth(genv, env),
            // Follow the synthesis rules for unary operations.
            Rvalue::UnApp(un_op, op) => {
                let (param_ty, ret_ty) = match un_op {
                    // the `-` operator receives an integer and returns an integer of the same
                    // type.
                    UnOp::Neg(sign, size) => (BaseTy::Int(*sign, *size), BaseTy::Int(*sign, *size)),
                    // the `!` operator receives a booolean and returns a boolean.
                    UnOp::Not => (BaseTy::Bool, BaseTy::Bool),
                };

                // Synthetize the type of the operand
                let op_ty1 = op.synth(genv, env);
                // The type of the operand must have the type that the operator receives as base
                // type.
                assert_eq!(op_ty1.get_base(), Some(param_ty));

                // Resolve the operand into a predicate. This is possible because operands are
                // literals or locals.
                let op = Box::new(env.resolve_operand(op));

                // Return the `{ b : B | b == (un_op op) }` type.
                Ty::Refined(
                    ret_ty,
                    Predicate::Var(Variable::Bound).eq(ret_ty, Predicate::UnaryOp(*un_op, op)),
                )
            }
            // Follow the synthesis rules for binary operations.
            Rvalue::BinApp(bin_op, op1, op2) => {
                let (op_ty, ret_ty) = match bin_op {
                    // Arithmetic operators receive two integers of the same type and return an
                    // integer of the same type.
                    BinOp::Add(sign, size)
                    | BinOp::Sub(sign, size)
                    | BinOp::Mul(sign, size)
                    | BinOp::Div(sign, size)
                    | BinOp::Rem(sign, size) => {
                        (BaseTy::Int(*sign, *size), BaseTy::Int(*sign, *size))
                    }
                    // Rust's MIR does not have boolean binary operators. They are here just to be
                    // reused in predicates.
                    BinOp::And | BinOp::Or => unreachable!(),
                    // Equality operators receive two operands of the same type and return a
                    // boolean.
                    BinOp::Eq(ty) | BinOp::Neq(ty) => (*ty, BaseTy::Bool),
                    // Comparison operators receive two integers of the same type and return a
                    // boolean.
                    BinOp::Lt(sign, size)
                    | BinOp::Gt(sign, size)
                    | BinOp::Lte(sign, size)
                    | BinOp::Gte(sign, size) => (BaseTy::Int(*sign, *size), BaseTy::Bool),
                };
                // Synthetize the types of the operands.
                let op_ty1 = op1.synth(genv, env);
                let op_ty2 = op2.synth(genv, env);

                // The type of the operands should be the same.
                //
                // FIXME: this is not the case for the offset and shift operators.
                assert!(op_ty1.shape_eq(&op_ty2));
                // The type of the operands must have the type that the operator receives as base
                // type.
                assert_eq!(op_ty1.get_base(), Some(op_ty));

                // Resolve the operands into predicates. This is possible because operands are
                // literals or locals.
                let op1 = Box::new(env.resolve_operand(op1));
                let op2 = Box::new(env.resolve_operand(op2));

                // Return the `{ b : B | b == (op1 bin_op op2) }` type.
                Ty::Refined(
                    ret_ty,
                    Predicate::Var(Variable::Bound)
                        .eq(ret_ty, Predicate::BinaryOp(*bin_op, op1, op2)),
                )
            }
        }
    }
}
