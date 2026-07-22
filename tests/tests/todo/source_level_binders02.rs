extern crate flux_alloc;
use flux_attrs::*;

pub struct Berry {
    seeds: usize,
}

#[refined_by(fruits: int, nuts: int)]
#[invariant(nuts < fruits)]
pub struct Salad {
    #[field(usize[fruits])]
    fruits: usize,
    #[field(usize[nuts])]
    nuts: usize,
    berry: Option<Berry>,
}

#[spec(fn (s: &mut Salad) ensures s: Salad)]
pub fn amp(s: &mut Salad) {
    let fs = s.fruits;
    s.nuts = fs + 1;
    let ns = s.nuts;
    s.fruits = ns + 1;
}
