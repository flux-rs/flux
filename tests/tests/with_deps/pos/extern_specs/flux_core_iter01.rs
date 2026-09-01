extern crate flux_core;

use flux_rs::assert;

#[flux_rs::trusted]
#[flux_rs::spec(fn(&std::iter::Skip<I>[@size]) -> usize[size])]
fn skip_size<I>(_: &std::iter::Skip<I>) -> usize {
    unimplemented!()
}

pub fn test_exhausted_skip_preserves_size() {
    let mut it = [0_i32; 0].iter().skip(0);
    let _ = it.next();
    assert(skip_size(&it) == 0);
    let _ = it.next();
    assert(skip_size(&it) == 0);
}
