extern crate flux_alloc;
use flux_rs::attrs::*;

#[refined_by(fruits: int, nuts: int)]
#[invariant(nuts < fruits)]
struct Salad {
    #[field(usize[fruits])]
    fruits: usize,
    #[field(usize[nuts])]
    nuts: usize,
}

#[spec(fn (s: &mut Salad) ensures s: Salad)]
fn amp(s: &mut Salad) {
    let fs = s.fruits;
    s.nuts = fs + 1;
    let ns = s.nuts;
    s.fruits = ns + 1;
}
