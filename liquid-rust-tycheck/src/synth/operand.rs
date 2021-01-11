use crate::{env::Env, result::TyResult, synth::Synth};

use liquid_rust_mir::Operand;
use liquid_rust_ty::Ty;

impl<'a, S: Clone> Synth<'a, S> for Operand {
    type Ty = Ty;
    type Envs = &'a Env;

    fn synth(&self, env: Self::Envs) -> TyResult<S, Self::Ty> {
        match self {
            Operand::Literal(lit) => Ok(Ty::singleton(*lit)),
            Operand::Local(local) => {
                let var = env.resolve_local(*local);
                let ty = env.get_ty(var).clone();
                Ok(ty.selfify(var))
            }
        }
    }
}
