use crate::{check::Check, env::Env, result::TyResult, subtype::Subtype, synth::Synth};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{ty::Ty, Rvalue};

impl<'ty, 'env> Check<'ty, 'env> for Rvalue {
    type Ty = &'ty Ty;
    type Env = &'env Env;

    fn check(&self, ty: Self::Ty, emitter: &mut Emitter, env: Self::Env) -> TyResult {
        let synth_ty = self.synth(env)?;

        synth_ty.subtype(&ty, emitter, env)
    }
}
