use crate::{local_env::LocalEnv, synth::Synth};

use liquid_rust_mir::{
    ty::{Predicate, Ty},
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
                let base_ty = ty.get_base().unwrap();

                Ty::Refined(
                    base_ty,
                    Predicate::Bound.eq(base_ty, Predicate::Var(local.into())),
                )
            }
        }
    }
}
