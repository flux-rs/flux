use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(size: int)]
struct Skip<I>;

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
