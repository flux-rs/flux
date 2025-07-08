use flux_rs::extern_spec;

#[flux_rs::extern_spec(std::iter)]
trait IntoIterator {
    #[flux_rs::sig(fn(self: Self) -> Self::IntoIter)]
    fn into_iter(self) -> Self::IntoIter
    where
        Self: Sized;
}

#[flux_rs::extern_spec(core::ops)]
impl<I: Iterator> IntoIterator for I {
    #[flux_rs::sig(fn(self: I[@s]) -> I[s])]
    fn into_iter(self) -> I;
}
