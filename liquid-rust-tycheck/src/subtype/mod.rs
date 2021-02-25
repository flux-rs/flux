mod local_env;
mod ty;

pub(crate) trait Subtype<'env, Rhs = Self> {
    type Env: 'env;

    fn subtype(self, other: Rhs, env: Self::Env);
}
