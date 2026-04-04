extern crate flux_core;
use flux_rs::assert;

pub fn test_saturating_i32() {
    let x: i32 = 5;
    let y: i32 = 10;
    let z: i32 = i32::MAX - 5;
    let w: i32 = i32::MIN + 5;
    // saturating_sub: unsaturated case
    assert(y.saturating_sub(x) == 5);
    // saturating_sub: saturated at MIN
    assert(w.saturating_sub(y) == i32::MIN);
    // saturating_add: unsaturated case
    assert(x.saturating_add(y) == 15);
    // saturating_add: saturated at MAX
    assert(z.saturating_add(y) == i32::MAX);
    // saturating_add with negative rhs: saturated at MIN
    assert(w.saturating_add(-y) == i32::MIN);
}

pub fn test_abs_i32() {
    // Positive value is unchanged
    assert(10i32.abs() == 10);
    // Negative value is negated
    assert((-10i32).abs() == 10);
    // Zero is unchanged
    assert(0i32.abs() == 0);
}

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

pub fn test_saturating_u64() {
    let x: u64 = 5;
    let y: u64 = 10;
    let z: u64 = u64::MAX - 5;
    // saturating_sub: unsaturated case
    assert(y.saturating_sub(x) == 5);
    // saturating_sub: saturated case
    assert(x.saturating_sub(y) == 0);
    // saturating_add: unsaturated case
    assert(x.saturating_add(y) == 15);
    // saturating_add: saturated case
    assert(z.saturating_add(y) == u64::MAX);
}
