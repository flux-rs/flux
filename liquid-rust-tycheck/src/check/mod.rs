mod bblock;
mod operand;
mod rvalue;
mod terminator;

pub(crate) trait Check<'ty, 'env> {
    type Env: 'env;
    type Ty: 'ty;

    fn check(&self, ty: Self::Ty, env: Self::Env);
}
