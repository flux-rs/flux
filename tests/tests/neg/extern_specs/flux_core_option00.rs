extern crate flux_core;
use flux_rs::assert;

// --- expect ---

pub fn test_expect(x: Option<i32>) {
    let _ = x.expect("oops"); //~ ERROR refinement type error
}

// --- and ---

pub fn test_and(x: Option<i32>, y: Option<i32>) {
    assert(x.and(y).is_some()); //~ ERROR refinement type error
}

// --- or ---

pub fn test_or(x: Option<i32>, y: Option<i32>) {
    assert(x.or(y).is_none()); //~ ERROR refinement type error
}

// --- map ---

pub fn test_map(x: Option<i32>) {
    assert(x.map(|v| v + 1).is_some()); //~ ERROR refinement type error
}
