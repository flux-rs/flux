use crate::Fixpoint;

pub(crate) trait Embed {
    type Output;

    fn embed(&self, fixpoint: &Fixpoint) -> Self::Output;
}
