use crate::{check::Check, local_env::LocalEnv};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{ty::Ty, Operand, Rvalue};

impl<'ty, 'env> Check<'ty, 'env> for Operand {
    type Ty = &'ty Ty;
    type Env = (&'env LocalEnv, &'env mut Emitter);

    fn check(&self, ty: Self::Ty, env: Self::Env) {
        let rvalue = Rvalue::Use(self.clone());
        rvalue.check(ty, env)
    }
}
