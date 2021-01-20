use crate::{env::Env, result::TyResult, synth::Synth};

use liquid_rust_mir::Operand;
use liquid_rust_ty::{Ty, Variable};

impl<'env> Synth<'env> for Operand {
    type Ty = Ty;
    type Env = &'env Env;

    fn synth(&self, env: Self::Env) -> TyResult<Self::Ty> {
        match self {
            Operand::Literal(lit) => Ok(Ty::singleton(*lit)),
            Operand::Local(local) => {
                let ty = env.get_ty(*local).clone();
                Ok(ty.selfify(Variable::Local((*local).into())))
            }
        }
    }
}
