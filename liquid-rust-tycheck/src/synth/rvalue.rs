use crate::{local_env::LocalEnv, synth::Synth};

use liquid_rust_mir::{
    ty::{BaseTy, BinOp, Predicate, Ty, UnOp},
    Rvalue,
};

impl<'env> Synth<'env> for Rvalue {
    type Ty = Ty;
    type Env = &'env LocalEnv;

    fn synth(&self, env: Self::Env) -> Self::Ty {
        match self {
            Rvalue::Use(operand) => operand.synth(env),
            Rvalue::UnApp(un_op, op) => {
                let (param_ty, ret_ty) = match un_op {
                    // the `-` operator receives an integer and returns an integer of the same
                    // type.
                    UnOp::Neg(sign, size) => (BaseTy::Int(*sign, *size), BaseTy::Int(*sign, *size)),
                    // the `!` operator receives a booolean and returns a boolean.
                    UnOp::Not => (BaseTy::Bool, BaseTy::Bool),
                };

                // Synthetize the type of the operand
                let op_ty1 = op.synth(env);
                // The type of the operand must have the type that the operator receives as base
                // type.
                assert!(op_ty1.has_base(param_ty));
                //
                // Resolve the operand into a predicate. This is possible because operands are
                // literals or locals.
                let op = Box::new(Predicate::from(op.clone()));

                // Return the `{ b : B | b == (un_op op) }` type.
                Ty::Refined(
                    ret_ty,
                    Predicate::Bound.eq(ret_ty, Predicate::UnaryOp(*un_op, op)),
                )
            }
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
                let op_ty1 = op1.synth(env);
                let op_ty2 = op2.synth(env);

                // The type of the operands should be the same.
                //
                // FIXME: this is not the case for the offset and shift operators.
                assert!(op_ty1.shape_eq(&op_ty2));

                // The type of the operands must have the type that the operator receives as base
                // type.
                assert!(op_ty1.has_base(op_ty));

                // Resolve the operands into predicates. This is possible because operands are
                // literals or locals.
                let op1 = Box::new(Predicate::from(op1.clone()));
                let op2 = Box::new(Predicate::from(op2.clone()));

                // Return the `{ b : B | b == (op1 bin_op op2) }` type.
                Ty::Refined(
                    ret_ty,
                    Predicate::Bound.eq(ret_ty, Predicate::BinaryOp(*bin_op, op1, op2)),
                )
            }
        }
    }
}
