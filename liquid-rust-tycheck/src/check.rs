use crate::{
    env::Env,
    glob_env::GlobEnv,
    result::{TyError, TyErrorKind, TyResult},
    synth::Synth,
};

use liquid_rust_common::index::Index;
use liquid_rust_mir::{
    BBlock, Local, Operand, Statement, StatementKind, Terminator, TerminatorKind,
};
use liquid_rust_ty::{BaseTy, Literal, Predicate, Ty, Variable};

/// Rule to check that a term has a valid type.
pub trait Check<S> {
    /// Check that `self` has type `ty` under the environments `genv` and `env`.
    fn check(&self, genv: &GlobEnv<S>, env: &mut Env<S>, ty: &Ty) -> TyResult<S>;
}

impl<S: Clone> Check<S> for BBlock<S> {
    fn check(&self, genv: &GlobEnv<S>, env: &mut Env<S>, ty: &Ty) -> TyResult<S> {
        // Follow the `Chk-Blk` rule.
        let unit = BaseTy::Unit.refined();
        // Check that every statement in the block has type unit.
        for statement in self.statements() {
            statement.check(genv, env, &unit)?;
        }
        // Then the basic block has `ty` type if the terminator has `ty` type.
        self.terminator().check(genv, env, ty)
    }
}

impl<S: Clone> Check<S> for Statement<S> {
    fn check(&self, genv: &GlobEnv<S>, env: &mut Env<S>, ty: &Ty) -> TyResult<S> {
        let unit = BaseTy::Unit.refined();
        // All statements have type unit. Checking for any other type is an error.
        if !unit.shape_eq(ty) {
            return Err(TyError {
                kind: TyErrorKind::ShapeMismatch {
                    expected: unit.clone(),
                    found: ty.clone(),
                },
                span: self.span.clone(),
            });
        }

        match &self.kind {
            // If the statement is a noop there is nothing to do.
            StatementKind::Noop => Ok(()),
            // If the statement is an assignment, follow the `Syn-Assign` rule.
            StatementKind::Assign(lhs, rhs) => {
                // Synthetize a type for the right-hand side of the assignment.
                let rhs_ty = rhs.synth(genv, env);

                // Get the type of the light-hand side of the assignment from the environment.
                let variable = env.resolve_local(*lhs);
                let lhs_ty = env.get_ty(variable);

                // Both sides must have types with the same shape for this assignment to be valid.
                if !rhs_ty.shape_eq(lhs_ty) {
                    return Err(TyError {
                        kind: TyErrorKind::ShapeMismatch {
                            expected: lhs_ty.clone(),
                            found: rhs_ty.clone(),
                        },
                        span: self.span.clone(),
                    });
                }

                // Annotate the left-hand side local with the right-hand side type. This introduces
                // a new local variable for the left-hand side local instead of overwriting the
                // type for the old local variable.
                env.annotate_local(*lhs, rhs_ty);

                Ok(())
            }
        }
    }
}

impl<S: Clone> Check<S> for Terminator<S> {
    fn check(&self, genv: &GlobEnv<S>, env: &mut Env<S>, ty: &Ty) -> TyResult<S> {
        match &self.kind {
            // Follow the `Chk-Ret` rule.
            TerminatorKind::Return => {
                // The type of a `return` terminator is the type of the `_0` local.
                let variable = env.resolve_local(Local::first());
                env.check_syn(genv, &variable, ty, self.span.clone())
            }
            // Follow the `Chk-Goto` rule.
            TerminatorKind::Goto(target) => {
                // The type of a `goto` terminator is the type of the target block.
                genv.get_bblock(*target).check(genv, env, ty)
            }
            // Follow the `Chk-Assert` rule.
            TerminatorKind::Assert(cond, expected, target) => {
                // An assertion is well-typed if `cond` has type `{b : bool | expected}`.
                env.check_syn(
                    genv,
                    cond,
                    &Ty::singleton(Literal::from(*expected)),
                    self.span.clone(),
                )?;
                // Then, the type of the assertion is the type of the target block.
                genv.get_bblock(*target).check(genv, env, ty)
            }
            // Follow the `Chk-Call` rule.
            TerminatorKind::Call(lhs, func, args, bb_id) => {
                // Retrieve all the arguments of the call as predicates.
                let pred_args: Vec<Predicate> = args
                    .into_iter()
                    .map(|arg| env.resolve_operand(arg))
                    .collect();

                // Get the type of the called function and project its indexed arguments to the
                // arguments of the call. It is OK to do all the projections at once because each
                // indexed argument is cannot appear in its own type, just in the types of the next
                // indexed arguments.
                let func_ty = genv
                    .get_func(*func)
                    .ty()
                    .clone()
                    .project_args(|pos| pred_args[pos].clone());

                // Check that each call argument has the type of the argument of the called
                // function.
                for (arg_ty, op) in func_ty.arguments().iter().zip(args.into_iter()) {
                    env.check_syn(genv, op, arg_ty, self.span.clone())?;
                }

                // Retrieve the return type of the function. This is free of indexed arguments
                // because it was already projected.
                let rhs_ty = func_ty.return_ty();

                // Get the type of the left-hand side local of the call.
                let variable = env.resolve_local(*lhs);
                let lhs_ty = env.get_ty(variable);

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
                env.annotate_local(*lhs, rhs_ty.clone());

                // Then, the type of the call is the type of the target block.
                genv.get_bblock(*bb_id).check(genv, env, ty)
            }
            // Follow the `Chk-Switch` rule.
            TerminatorKind::Switch(local, branches, default) => {
                // Synthetize the type of the local. Keep the predicate to be able to constraint it
                // for the default branch.
                let (base_ty, mut pred) = match Operand::Local(*local).synth(genv, env) {
                    Ty::Refined(base_ty, pred) => (base_ty, pred),
                    // Locals cannot be functions yet.
                    _ => unreachable!(),
                };

                let var = env.resolve_local(*local);

                // A switch terminator is well-typed if all its branches are well-typed.
                for &(bits, target) in branches.as_ref() {
                    let lit = Literal::new(bits, base_ty);
                    let op_ty = Ty::singleton(lit).selfify(var);

                    env.fork(move |env| {
                        // Annotate the local with the singleton type for the literal of the
                        // branch.
                        env.annotate_local(*local, op_ty);
                        genv.get_bblock(target).check(genv, env, ty)
                    })?;

                    // The local cannot be equal to the branch literal outside the branch.
                    pred = pred & Predicate::Var(Variable::Bound).neq(base_ty, lit);
                }

                // Annotate the local with a type refined to ensure that the local was not equal to
                // any of the literals in the branches.
                env.annotate_local(*local, Ty::Refined(base_ty, pred));
                genv.get_bblock(*default).check(genv, env, ty)
            }
        }
    }
}
