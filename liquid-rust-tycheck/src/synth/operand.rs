use crate::{local_env::LocalEnv, synth::Synth};

use liquid_rust_mir::{
    ty::{Ty, Variable},
    Operand,
};

impl<'env> Synth<'env> for Operand {
    type Ty = Ty;
    type Env = &'env LocalEnv;

    fn synth(&self, env: Self::Env) -> Self::Ty {
        match *self {
            Operand::Literal(lit) => (Ty::singleton(lit)),
            Operand::Local(local) => {
                let ty = env.get_ty(local.into()).unwrap().clone();
                // Maybe we only need the base type
                ty.selfify(Variable::from(local))
            }
        }
    }
}
