use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(inner: I)]
struct Map<I, F>;

#[extern_spec(core::iter)]
#[assoc(
    fn size(x: Map<I>) -> int { <I as Iterator>::size(x.inner) }
    fn done(x: Map<I>) -> bool { <I as Iterator>::done(x.inner) }
    fn step(x: Map<I>, y: Map<I>) -> bool { <I as Iterator>::step(x.inner, y.inner) }
)]
impl<B, I: Iterator, F: FnMut(I::Item) -> B> Iterator for Map<I, F> {
    #[spec(fn(self: &mut Self[@curr_s]) -> Option<B>[!<Self as Iterator>::done(curr_s)]
             ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)})]
    fn next(&mut self) -> Option<B>;
}
