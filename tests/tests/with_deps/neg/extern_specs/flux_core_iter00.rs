extern crate flux_core;
use flux_rs::assert;

#[flux_rs::trusted]
#[flux_rs::spec(fn(&std::iter::Take<I>[@n, @inner]) -> usize[n])]
fn take_remaining<I>(_: &std::iter::Take<I>) -> usize {
    unimplemented!()
}

// Calling `next` after `take(0)` is exhausted must not create an impossible negative count.
pub fn test_exhausted_take_does_not_create_false_context() {
    let xs: [i32; 0] = [];
    let mut iter = xs.iter().take(0);
    let _ = iter.next();
    let _ = take_remaining(&iter);
    assert(false); //~ ERROR refinement type error
}
