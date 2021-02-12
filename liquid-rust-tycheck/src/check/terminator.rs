use crate::{
    bblock_env::BBlockEnv, check::Check, func_env::FuncEnv, local_env::LocalEnv, subtype::Subtype,
    synth::Synth,
};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{
    ty::{BaseTy, Literal, Predicate, Ty, UnOp, Variable},
    Local, Operand, Terminator, TerminatorKind,
};

impl<'ty, 'env> Check<'ty, 'env> for Terminator {
    type Ty = LocalEnv;
    type Env = (&'env FuncEnv, &'env BBlockEnv, &'env Ty, &'env mut Emitter);

    fn check(&self, mut ty: Self::Ty, (func_env, bb_env, return_ty, emitter): Self::Env) {
        match &self.kind {
            TerminatorKind::Return => {
                let return_local = Operand::Local(Local::ret());

                return_local.check(return_ty, (&ty, emitter))
            }
            TerminatorKind::Goto(target) => {
                let target_ty = bb_env.get_ty(*target).unwrap().clone();
                ty.subtype(target_ty, emitter)
            }
            TerminatorKind::Assert(cond, expected, target) => {
                let cond_ty = if *expected {
                    Ty::Refined(BaseTy::Bool, Predicate::Bound)
                } else {
                    Ty::Refined(
                        BaseTy::Bool,
                        Predicate::UnaryOp(UnOp::Not, Box::new(Predicate::Bound)),
                    )
                };
                // An assertion is well-typed if `cond` has type `{b : bool | b == expected}`.
                cond.check(&cond_ty, (&ty, emitter));
                // Then, the type of the assertion is the type of the target block.
                let target_ty = bb_env.get_ty(*target).unwrap().clone();
                ty.subtype(target_ty, emitter)
            }
            TerminatorKind::Call(lhs, func, args, target) => {
                // Retrieve all the arguments of the call as predicates.
                let pred_args: Vec<Predicate> =
                    args.into_iter().map(|arg| arg.clone().into()).collect();

                // Get the type of the called function and project its indexed arguments to the
                // arguments of the call. It is OK to do all the projections at once because each
                // indexed argument is cannot appear in its own type, just in the types of the next
                // indexed arguments.
                let func_ty = func_env
                    .get_ty(*func)
                    .unwrap()
                    .clone()
                    .project_args(|pos| pred_args[pos].clone());

                // Check that each call argument has the type of the argument of the called
                // function.
                for (arg_ty, op) in func_ty.arguments().iter().zip(args.into_iter()) {
                    op.check(arg_ty, (&ty, emitter));
                }

                // Retrieve the return type of the function. This is free of indexed arguments
                // because it was already projected.
                let rhs_ty = func_ty.return_ty();

                // Get the type of the left-hand side local of the call.
                let lhs_ty = ty.get_ty((*lhs).into()).unwrap();

                // The return type and the type of the left-hand side must have the same shape.
                assert!(rhs_ty.shape_eq(lhs_ty));

                // Annotate the left-hand side local with the return type. This introduces a new
                // local variable for the left-hand side local instead of overwriting the type for
                // the old local variable.
                ty.rebind((*lhs).into(), rhs_ty.clone());

                // Then, the type of the call is the type of the target block.
                let target_ty = bb_env.get_ty(*target).unwrap().clone();
                ty.subtype(target_ty, emitter)
            }
            TerminatorKind::Switch(local, branches, default) => {
                // Synthetize the type of the local. Keep the predicate to be able to constraint it
                // for the default branch.
                let (base_ty, mut pred) = match Operand::Local(*local).synth(&ty) {
                    Ty::Refined(base_ty, pred) => (base_ty, pred),
                    // Locals cannot be functions yet.
                    _ => unreachable!(),
                };

                let var = Variable::Local((*local).into());

                // A switch terminator is well-typed if all its branches are well-typed.
                for &(bits, target) in branches.as_ref() {
                    let lit = Literal::new(bits, base_ty);
                    let op_ty = Ty::singleton(lit).selfify(var);

                    // Annotate the local with the singleton type for the literal of the
                    // branch.
                    let mut ty = ty.clone();
                    ty.rebind((*local).into(), op_ty);

                    let target_ty = bb_env.get_ty(target).unwrap().clone();
                    ty.subtype(target_ty, emitter);

                    // The local cannot be equal to the branch literal outside the branch.
                    pred = pred & Predicate::Bound.neq(base_ty, lit);
                }

                // Annotate the local with a type refined to ensure that the local was not equal to
                // any of the literals in the branches.
                ty.rebind((*local).into(), Ty::Refined(base_ty, pred));

                let default_ty = bb_env.get_ty(*default).unwrap().clone();
                ty.subtype(default_ty, emitter)
            }
        }
    }
}
