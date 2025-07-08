use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(a: A, b: B, idx: int, len: int, a_len: int)]
struct Zip<A, B>;

#[extern_spec(core::iter)]
// VTOCK todo: Is this really the right thing (see A::MAY_HAVE_SIDE_EFFECT)
#[assoc(fn size(r: Zip<A, B>) -> int { r.len })]
#[assoc(fn done(r: Zip<A, B>) -> bool { r.idx >= r.len && r.idx >= r.a_len })]
#[assoc(fn step(self: Zip<A, B>, other: Zip<A, B>) -> bool { self.idx + 1 == other.idx } )]
impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    #[flux_rs::sig(fn(&mut Zip<A, B>[@a, @b, @idx, @len, @a_len]) -> Option<_>[idx >= len || idx >= a_len])]
    fn next(&mut self) -> Option<<Zip<A, B> as Iterator>::Item>;
}
