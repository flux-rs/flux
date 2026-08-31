use flux_attrs::*;

defs! {
    use crate::num::min;
}

/// `Take` is refined by the number of elements left to take (`n`) together with the inner
/// iterator, so that `done` can be stated exactly: a `Take` is exhausted when it has taken its
/// quota *or* the inner iterator has run out. Refining by `n` alone would let `next` claim a
/// `Some` that the inner iterator cannot supply.
#[extern_spec(core::iter)]
#[refined_by(n: int, inner: I)]
struct Take<I>;

#[extern_spec(core::iter)]
#[assoc(
    fn size(x: Take<I>) -> int { min(x.n, <I as Iterator>::size(x.inner)) }
    fn done(x: Take<I>) -> bool { x.n <= 0 || <I as Iterator>::done(x.inner) }
    fn step(x: Take<I>, y: Take<I>) -> bool {
        if x.n > 0 {
            y.n == x.n - 1 && <I as Iterator>::step(x.inner, y.inner)
        } else {
            y.n == x.n && y.inner == x.inner
        }
    }
)]
impl<I: Iterator> Iterator for Take<I> {
    #[spec(
        fn(self: &mut Self[@curr_s]) -> Option<_>[!<Self as Iterator>::done(curr_s)]
        ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)}
    )]
    fn next(&mut self) -> Option<I::Item>;
}
