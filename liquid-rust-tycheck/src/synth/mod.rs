mod operand;
mod rvalue;
mod statement;

pub(crate) trait Synth<'env> {
    type Ty;
    type Env: 'env;

    fn synth(&self, env: Self::Env) -> Self::Ty;
}
