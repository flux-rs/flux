use crate::{
    env::Env,
    result::{TyError, TyErrorKind, TyResult},
    synth::Synth,
};

use liquid_rust_mir::{Statement, StatementKind};

impl<'a, S: Clone> Synth<'a, S> for Statement<S> {
    type Ty = Env;
    type Envs = &'a Env;

    fn synth(&self, env: Self::Envs) -> TyResult<S, Self::Ty> {
        match &self.kind {
            StatementKind::Noop => Ok(env.clone()),
            StatementKind::Assign(lhs, rhs) => {
                // Synthetize a type for the right-hand side of the assignment.
                let rhs_ty = rhs
                    .synth(env)
                    .map_err(|err| err.with_span(self.span.clone()))?;

                // Get the type of the left-hand side of the assignment from the environment.
                let lhs_ty = env.get_ty(*lhs);

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

                // The left-hand side has the type of the right hand side in the new environment.
                let mut output = env.clone();
                output.rebind_local(*lhs, rhs_ty);

                Ok(output)
            }
        }
    }
}
