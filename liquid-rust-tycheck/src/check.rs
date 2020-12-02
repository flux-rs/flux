use crate::{
    env::Env,
    glob_env::GlobEnv,
    result::{TyError, TyResult},
    synth::Synth,
    ty::{Predicate, Ty},
};

use liquid_rust_common::index::Index;
use liquid_rust_mir::{BBlock, Local, Statement, Terminator};
use liquid_rust_ty::{BaseTy, Literal};

pub(super) trait Check {
    fn check(&self, genv: &GlobEnv, env: &mut Env, ty: &Ty) -> TyResult;
}

impl Check for BBlock {
    fn check(&self, genv: &GlobEnv, env: &mut Env, ty: &Ty) -> TyResult {
        for statement in self.statements() {
            statement.check(genv, env, &BaseTy::Unit.refined())?;
        }

        self.terminator().check(genv, env, ty)
    }
}

impl Check for Statement {
    fn check(&self, genv: &GlobEnv, env: &mut Env, ty: &Ty) -> TyResult {
        let unit = BaseTy::Unit.refined();

        if !unit.shape_eq(ty) {
            return Err(TyError::ShapeMismatch(unit, ty.clone()));
        }

        match self {
            Statement::Noop => Ok(()),
            // Syn-Assign
            Statement::Assign(lhs, rhs) => {
                let rhs_ty = rhs.synth(genv, env);

                let variable = env.resolve_local(*lhs);
                let lhs_ty = env.get_ty(variable);

                if !rhs_ty.shape_eq(lhs_ty) {
                    return Err(TyError::ShapeMismatch(rhs_ty, lhs_ty.clone()));
                }

                env.annotate_local(*lhs, rhs_ty);

                Ok(())
            }
        }
    }
}

impl Check for Terminator {
    fn check(&self, genv: &GlobEnv, env: &mut Env, ty: &Ty) -> TyResult {
        match self {
            // Chk-Ret
            Terminator::Return => {
                let variable = env.resolve_local(Local::first());
                variable.check(genv, env, ty)
            }
            // Chk-Goto
            Terminator::Goto(bb_id) => genv.get_bblock(*bb_id).check(genv, env, ty),
            // Chk-Assert
            Terminator::Assert(cond, expected, bb_id) => {
                cond.check(genv, env, &Ty::singleton(Literal::from(*expected)))?;
                genv.get_bblock(*bb_id).check(genv, env, ty)
            }
            // Chk-Call
            Terminator::Call(lhs, func, args, bb_id) => {
                let pred_args: Vec<Predicate> = args
                    .into_iter()
                    .map(|arg| env.resolve_operand(arg))
                    .collect();

                let func_ty = genv
                    .get_func(*func)
                    .ty()
                    .clone()
                    .project_args(|pos| pred_args[pos].clone());

                for (arg_ty, op) in func_ty.arguments().iter().zip(args.into_iter()) {
                    op.check(genv, env, arg_ty)?;
                }

                let rhs_ty = func_ty.return_ty();

                let variable = env.resolve_local(*lhs);
                let lhs_ty = env.get_ty(variable);

                if !rhs_ty.shape_eq(lhs_ty) {
                    return Err(TyError::ShapeMismatch(rhs_ty.clone(), lhs_ty.clone()));
                }

                env.annotate_local(*lhs, rhs_ty.clone());

                genv.get_bblock(*bb_id).check(genv, env, ty)
            }
        }
    }
}

// Chk-Syn
impl<T: Synth> Check for T {
    fn check(&self, genv: &GlobEnv, env: &mut Env, ty: &Ty) -> TyResult {
        let synth_ty = self.synth(genv, env);
        env.is_subtype(&synth_ty, ty)
    }
}
