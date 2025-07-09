use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(size: int)]
struct Skip<I>;

#[extern_spec(core::iter)]
#[assoc(fn size(r: Skip) -> int { r.size } )]
#[assoc(fn step(self: Skip, other: Skip) -> bool { other.size == self.size - 1 } )]
impl<I: Iterator> Iterator for Skip<I> {}
