extern crate flux_core;
use flux_rs::assert;

pub fn test_saturating_usize() {
    let x: usize = 5;
    let y: usize = 10;
    let z: usize = usize::MAX - 5;
    // saturating_sub: unsaturated case
    assert(y.saturating_sub(x) == 5);
    // saturating_sub: saturated case
    assert(x.saturating_sub(y) == 0);
    // saturating_add: unsaturated case
    assert(x.saturating_add(y) == 15);
    // saturating_add: saturated case
    assert(z.saturating_add(y) == usize::MAX);
}

pub fn saturating_u32() {
    let x: u32 = 5;
    let y: u32 = 10;
    let z: u32 = u32::MAX - 5;
    // saturating_sub: unsaturated case
    assert(y.saturating_sub(x) == 5);
    // saturating_sub: saturated case
    assert(x.saturating_sub(y) == 0);
    // saturating_add: unsaturated case
    assert(x.saturating_add(y) == 15);
    // saturating_add: saturated case
    assert(z.saturating_add(y) == u32::MAX);
}