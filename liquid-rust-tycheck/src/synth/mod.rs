mod operand;
mod rvalue;
mod statement;

use crate::result::TyResult;

pub(crate) trait Synth<'env> {
    type Ty;
    type Env: 'env;

    fn synth(&self, envs: Self::Env) -> TyResult<Self::Ty>;
}
