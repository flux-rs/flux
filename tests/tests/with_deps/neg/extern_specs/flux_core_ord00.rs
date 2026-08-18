// Negative counterparts to `pos/extern_specs/flux_core_ord00.rs`.
extern crate flux_core;

use flux_rs::{assert, attrs::*};

// --- `min` and `max` are not interchangeable ---

#[spec(fn(x: usize, y: usize) -> usize[if x > y { x } else { y }])]
fn min_is_not_max(x: usize, y: usize) -> usize {
    x.min(y) //~ ERROR refinement type error
}

#[spec(fn(x: usize, y: usize) -> usize[if x < y { x } else { y }])]
fn max_is_not_min(x: usize, y: usize) -> usize {
    x.max(y) //~ ERROR refinement type error
}

// --- the bounds are the right way round ---

#[spec(fn(x: usize, y: usize))]
fn min_is_not_an_upper_bound(x: usize, y: usize) {
    let m = x.min(y);
    assert(x <= m); //~ ERROR refinement type error
}

#[spec(fn(x: usize, y: usize))]
fn max_is_not_a_lower_bound(x: usize, y: usize) {
    let m = x.max(y);
    assert(m <= x); //~ ERROR refinement type error
}

// `min` is not strictly less than both arguments; it may equal them.
#[spec(fn(x: usize, y: usize))]
fn min_is_not_strict(x: usize, y: usize) {
    let m = x.min(y);
    assert(m < x); //~ ERROR refinement type error
}

// --- concrete values ---

fn wrong_concrete() {
    assert(5usize.min(3) == 5); //~ ERROR refinement type error
}

// --- non-`usize` `Ord` impls have only the vacuous default ---

// `i32` does not define `min_res`, so nothing can be concluded about the result.
#[spec(fn(x: i32, y: i32) -> i32[if x < y { x } else { y }])]
fn i32_has_no_spec(x: i32, y: i32) -> i32 {
    x.min(y) //~ ERROR refinement type error
}
