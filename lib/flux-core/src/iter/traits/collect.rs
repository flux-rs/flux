use flux_attrs::*;

#[extern_spec]
#[flux::assoc(fn with_size(self: Self, n:int) -> bool { true })] // default: don't know!
trait FromIterator<A> {}

#[extern_spec(core::iter)]
trait IntoIterator {
    #[spec(fn(self: Self) -> Self::IntoIter)]
    fn into_iter(self) -> Self::IntoIter
    where
        Self: Sized;
}

#[extern_spec(core::ops)]
impl<I: Iterator> IntoIterator for I {
    #[spec(fn(self: I[@s]) -> I[s])]
    fn into_iter(self) -> I;
}
