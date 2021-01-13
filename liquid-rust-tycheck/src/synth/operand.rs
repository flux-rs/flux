use crate::{env::Env, result::TyResult, synth::Synth};

use liquid_rust_mir::Operand;
use liquid_rust_ty::{Ty, Variable};

impl<'a, S: Clone> Synth<'a, S> for Operand {
    type Ty = Ty;
    type Envs = &'a Env;

    fn synth(&self, env: Self::Envs) -> TyResult<S, Self::Ty> {
        match self {
            Operand::Literal(lit) => Ok(Ty::singleton(*lit)),
            Operand::Local(local) => {
                let ty = env.get_ty(*local).clone();
                Ok(ty.selfify(Variable::Local((*local).into())))
            }
        }
    }
}
