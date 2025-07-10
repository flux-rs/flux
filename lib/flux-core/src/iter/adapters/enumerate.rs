use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(idx: int, inner: I)]
struct Enumerate<I>;

#[extern_spec(core::iter)]
#[assoc(
    fn size(x: Enumerate<I>) -> int { <I as Iterator>::size(x.inner) }
    fn done(x: Enumerate<I>) -> bool { <I as Iterator>::done(x.inner) }
    fn step(x: Enumerate<I>, y: Enumerate<I>) -> bool { 
        x.idx + 1 == y.idx && <I as Iterator>::step(x.inner, y.inner)
    }
)]
impl<I: Iterator> Iterator for Enumerate<I> {
    #[spec(fn(self: &mut Enumerate<I>[@curr_s]) -> Option<(usize[curr_s.idx], _)>[!<I as Iterator>::done(curr_s.inner)]
           ensures self: Enumerate<I>{next_s: curr_s.idx + 1 == next_s.idx && <I as Iterator>::step(curr_s.inner, next_s.inner)})]
    fn next(&mut self) -> Option<(usize, <I as Iterator>::Item)>;
}
