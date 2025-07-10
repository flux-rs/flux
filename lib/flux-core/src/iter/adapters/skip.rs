use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(size: int)]
struct Skip<I>;

// TODO: See discussion here: https://github.com/flux-rs/flux/pull/1170#discussion_r2198219054
// We should store the number of skipped elements in the refined_by and compute the size
// based on the inner iterator here, but you can’t quite do that because that requires
// “stepping” the inner iterator N times (when you construct the Skip). We could possibly generalize
// the `step` to take an `int` count ...

#[extern_spec(core::iter)]
#[assoc(
    fn size(r: Skip) -> int { r.size }
    fn step(self: Skip, other: Skip) -> bool { other.size == self.size - 1 }
)]
impl<I: Iterator> Iterator for Skip<I> {
    #[spec(
        fn(self: &mut Self[@curr_s]) -> Option<_>[!<Self as Iterator>::done(curr_s)]
        ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)}
    )]
    fn next(&mut self) -> Option<I::Item>;
}
