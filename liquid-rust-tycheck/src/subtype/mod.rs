mod local_env;
mod ty;

pub(crate) trait Subtype<'env> {
    type Env: 'env;

    fn subtype(self, other: Self, env: Self::Env);
}
