use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(n: int, inner: I)]
struct Skip<I>;

#[extern_spec(core::iter)]
#[assoc(fn size(r: Skip<I>) -> int { <I as Iterator>::size(r.inner) } )]
#[assoc(fn done(r: Skip<I>) -> bool { <I as Iterator>::done(r.inner) } )]
#[assoc(fn step(self: Skip<I>, other: Skip<I>) -> bool { <I as Iterator>::step(self.inner, other.inner) } )]
impl<I: Iterator> Iterator for Skip<I> {
    #[flux_rs::sig(fn(&mut Skip<I>[@n, @inner]) -> Option<I::Item>[<I as Iterator>::done(inner)])]
    fn next(&mut self) -> Option<I::Item>;
}
