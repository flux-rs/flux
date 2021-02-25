use crate::{local_env::LocalEnv, subtype::Subtype, synth::Synth};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{
    ty::{Predicate, Ty, Variable},
    Operand,
};

impl<'env> Subtype<'env> for LocalEnv {
    type Env = &'env mut Emitter;

    fn subtype(mut self, mut other: Self, emitter: Self::Env) {
        while let Some(_) = other.first() {
            let (var, ty2) = other.remove_first();
            match var {
                Variable::Local(local) => {
                    let ty1 = Operand::Local(local).synth(&self);

                    ty1.subtype(&ty2, (&self, emitter));
                }
                Variable::Ghost(_) => {
                    self.bind(var, ty2);
                }
            }
        }
    }
}
