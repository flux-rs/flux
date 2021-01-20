use crate::{
    bblock_env::{BBlockEnv, BBlockTy},
    check::Check,
    glob_env::GlobEnv,
    result::{TyError, TyErrorKind, TyResult},
    synth::Synth,
};

use liquid_rust_mir::{Local, Operand, Terminator, TerminatorKind};
use liquid_rust_ty::{Literal, Predicate, Ty, Variable};

impl<'ty, 'env> Check<'ty, 'env> for Terminator {
    type Ty = &'ty BBlockTy;
    type Env = (&'env GlobEnv, &'env BBlockEnv, &'env Ty);

    fn check(&self, ty: Self::Ty, env: Self::Env) -> TyResult {
        print!("\nChk-Terminator: ");
        match &self.kind {
            TerminatorKind::Return => {
                let (_, _, return_ty) = env;
                let return_local = Operand::Local(Local::ret());

                return_local
                    .check(return_ty, &ty.input)
                    .map_err(|err| err.with_span(self.span.clone()))
            }
            TerminatorKind::Goto(target) => target.check(ty, env),
            TerminatorKind::Assert(cond, expected, target) => {
                // An assertion is well-typed if `cond` has type `{b : bool | expected}`.
                cond.check(&Ty::singleton(Literal::from(*expected)), &ty.input)
                    .map_err(|err| err.with_span(self.span.clone()))?;
                // Then, the type of the assertion is the type of the target block.
                target.check(ty, env)
            }
            TerminatorKind::Call(lhs, func, args, target) => {
                let (genv, _, _) = env;
                // Retrieve all the arguments of the call as predicates.
                let pred_args: Vec<Predicate> =
                    args.into_iter().map(|arg| arg.clone().into()).collect();

                // Get the type of the called function and project its indexed arguments to the
                // arguments of the call. It is OK to do all the projections at once because each
                // indexed argument is cannot appear in its own type, just in the types of the next
                // indexed arguments.
                let func_ty = genv
                    .get_ty(*func)
                    .clone()
                    .project_args(|pos| pred_args[pos].clone());

                // Check that each call argument has the type of the argument of the called
                // function.
                for (arg_ty, op) in func_ty.arguments().iter().zip(args.into_iter()) {
                    op.check(arg_ty, &ty.input)
                        .map_err(|err| err.with_span(self.span.clone()))?;
                }

                // Retrieve the return type of the function. This is free of indexed arguments
                // because it was already projected.
                let rhs_ty = func_ty.return_ty();

                // Get the type of the left-hand side local of the call.
                let lhs_ty = ty.input.get_ty(*lhs);

                // The return type and the type of the left-hand side must have the same shape.
                if !rhs_ty.shape_eq(lhs_ty) {
                    return Err(TyError {
                        kind: TyErrorKind::ShapeMismatch {
                            expected: lhs_ty.clone(),
                            found: rhs_ty.clone(),
                        },
                        span: self.span.clone(),
                    });
                }

                // Annotate the left-hand side local with the return type. This introduces a new
                // local variable for the left-hand side local instead of overwriting the type for
                // the old local variable.
                let mut ty = ty.clone();
                ty.input.rebind_local(*lhs, rhs_ty.clone());

                // Then, the type of the call is the type of the target block.
                target.check(&ty, env)
            }
            TerminatorKind::Switch(local, branches, default) => {
                // Synthetize the type of the local. Keep the predicate to be able to constraint it
                // for the default branch.
                let (base_ty, mut pred) = match Operand::Local(*local)
                    .synth(&ty.input)
                    .map_err(|err| err.with_span(self.span.clone()))?
                {
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
                    ty.input.rebind_local(*local, op_ty);

                    target.check(&ty, env)?;

                    // The local cannot be equal to the branch literal outside the branch.
                    pred = pred & Predicate::Var(Variable::Bound).neq(base_ty, lit);
                }

                // Annotate the local with a type refined to ensure that the local was not equal to
                // any of the literals in the branches.
                let mut ty = ty.clone();
                ty.input.rebind_local(*local, Ty::Refined(base_ty, pred));

                default.check(&ty, env)
            }
        }
    }
}
