use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(inner: I)]
struct Map<I, F>;

#[extern_spec(core::iter)]
#[assoc(fn size(x: Map<I>) -> int { <I as Iterator>::size(x.inner) })]
#[assoc(fn done(x: Map<I>) -> bool { <I as Iterator>::done(x.inner)})]
#[assoc(fn step(x: Map<I>, y: Map<I>) -> bool { <I as Iterator>::step(x.inner, y.inner)})]
impl<B, I: Iterator, F: FnMut(I::Item) -> B> Iterator for Map<I, F> {}
