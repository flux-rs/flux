use crate::{
    bblock_env::BBlockEnv, check::Check, func_env::FuncEnv, local_env::LocalEnv, subtype::Subtype,
    synth::Synth,
};

use liquid_rust_fixpoint::Emitter;
use liquid_rust_mir::{ty::Ty, BBlock, BBlockId};

impl<'ty, 'env> Check<'ty, 'env> for BBlock {
    type Ty = LocalEnv;
    type Env = (&'env FuncEnv, &'env BBlockEnv, &'env Ty, &'env mut Emitter);

    fn check(&self, mut ty: Self::Ty, env: Self::Env) {
        for statement in self.statements() {
            ty = statement.synth(ty);
        }

        self.terminator().check(ty, env)
    }
}

impl<'ty, 'env> Check<'ty, 'env> for BBlockId {
    type Ty = LocalEnv;
    type Env = (&'env FuncEnv, &'env BBlockEnv, &'env Ty, &'env mut Emitter);

    fn check(&self, ty: Self::Ty, (_, bb_env, _, emitter): Self::Env) {
        let bb_ty = bb_env.get_ty(*self).unwrap().clone();

        bb_ty.subtype(ty, emitter)
    }
}
