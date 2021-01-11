mod operand;
mod rvalue;
mod statement;

use crate::result::TyResult;

pub(crate) trait Synth<'env, S> {
    type Ty;
    type Envs: 'env;

    fn synth(&self, envs: Self::Envs) -> TyResult<S, Self::Ty>;
}
