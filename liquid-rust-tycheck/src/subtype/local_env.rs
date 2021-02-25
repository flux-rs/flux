use crate::{bblock_env::BBlockEnv, local_env::LocalEnv, subtype::Subtype, synth::Synth};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{ty::Variable, BBlockId, Operand};

impl<'env> Subtype<'env, BBlockId> for LocalEnv {
    type Env = (&'env mut BBlockEnv, &'env mut Emitter);

    fn subtype(mut self, other: BBlockId, (bb_env, emitter): Self::Env) {
        if let Some(mut other) = bb_env.get_ty(other).cloned() {
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
        } else {
            bb_env.initialize(other, self);
        }
    }
}
