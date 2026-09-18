extern crate flux_core;

#[flux_rs::trusted]
#[flux_rs::spec(fn(&std::iter::Skip<I>[@size]) -> usize[size])]
fn skip_size<I>(_: &std::iter::Skip<I>) -> usize {
    unimplemented!()
}

// Calling `next` on an exhausted `Skip` must not make its logical size negative.
// A negative size is inconsistent with `usize` and would let Flux prove `false`.
pub fn test_exhausted_skip_does_not_create_false_context() {
    let mut it = [0_i32; 0].iter().skip(0);
    let _ = it.next();
    let _ = skip_size(&it);
    flux_rs::assert(false); //~ ERROR refinement type error
}
