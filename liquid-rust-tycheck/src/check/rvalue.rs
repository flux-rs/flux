use crate::{check::Check, local_env::LocalEnv, subtype::Subtype, synth::Synth};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{ty::Ty, Rvalue};

impl<'ty, 'env> Check<'ty, 'env> for Rvalue {
    type Ty = &'ty Ty;
    type Env = (&'env LocalEnv, &'env mut Emitter);

    fn check(&self, ty: Self::Ty, (env, emitter): Self::Env) {
        let synth_ty = self.synth(env);

        synth_ty.subtype(&ty, (env, emitter));
    }
}
