use crate::{local_env::LocalEnv, synth::Synth};

use liquid_rust_mir::{Statement, StatementKind};

impl<'env> Synth<'env> for Statement {
    type Ty = LocalEnv;
    type Env = LocalEnv;

    fn synth(&self, mut env: Self::Env) -> Self::Ty {
        match &self.kind {
            StatementKind::Noop => env,
            StatementKind::Assign(lhs, rhs) => {
                let lhs = (*lhs).into();
                // Synthetize a type for the right-hand side of the assignment.
                let rhs_ty = rhs.synth(&env);
                // Get the type of the left-hand side of the assignment from the environment.
                let lhs_ty = env.get_ty(lhs).unwrap();

                // Both sides must have types with the same shape for this assignment to be valid.
                assert!(rhs_ty.shape_eq(lhs_ty));

                // The left-hand side has the type of the right hand side in the new environment.
                env.rebind(lhs, rhs_ty);

                env
            }
        }
    }
}
