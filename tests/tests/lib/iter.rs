use flux_rs::extern_spec;

#[extern_spec(std::iter)]
#[flux::assoc(fn size(x: Map<I>) -> int { <I as Iterator>::size(x.inner) })]
#[flux::assoc(fn done(x: Map<I>) -> bool { <I as Iterator>::done(x.inner)})]
#[flux::assoc(fn step(x: Map<I>, y: Map<I>) -> bool { <I as Iterator>::step(x.inner, y.inner)})]
impl<B, I: Iterator, F: FnMut(I::Item) -> B> Iterator for Map<I, F> {} // orig: where F: FnMut(I::Item) -> B {}

// -------------------------------------------------------------------------------------------------------------------------------------

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
