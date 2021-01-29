use crate::{check::Check, env::Env, result::TyResult};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{ty::Ty, Operand, Rvalue};

impl<'ty, 'env> Check<'ty, 'env> for Operand {
    type Ty = &'ty Ty;
    type Env = &'env Env;

    fn check(&self, ty: Self::Ty, emitter: &mut Emitter, env: Self::Env) -> TyResult {
        let rvalue = Rvalue::Use(self.clone());
        rvalue.check(ty, emitter, env)
    }
}
