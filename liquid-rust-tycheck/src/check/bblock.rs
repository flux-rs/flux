use crate::{
    bblock_env::BBlockEnv, check::Check, func_env::FuncEnv, local_env::LocalEnv, synth::Synth,
};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{ty::Ty, BBlock};

impl<'ty, 'env> Check<'ty, 'env> for BBlock {
    type Ty = LocalEnv;
    type Env = (
        &'env FuncEnv,
        &'env mut BBlockEnv,
        &'env Ty,
        &'env mut Emitter,
    );

    fn check(&self, mut ty: Self::Ty, env: Self::Env) {
        for statement in self.statements() {
            ty = statement.synth(ty);
        }

        self.terminator().check(ty, env)
    }
}
