use crate::{bblock_env::BBlockTy, result::TyResult, subtype::Subtype};

use liquid_rust_fixpoint::Emitter;

impl<'env> Subtype<'env> for BBlockTy {
    type Env = ();

    fn subtype(&self, other: &Self, emitter: &mut Emitter, env: Self::Env) -> TyResult {
        other.input.subtype(&self.input, emitter, env)?;
        self.output.subtype(&other.input, emitter, env)
    }
}
