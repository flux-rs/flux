// Specs for the provided methods `Ord::min`/`Ord::max`. The arithmetic lives in an associated
// refinement that only the `usize` impl defines; other `Ord` impls keep the vacuous default.
extern crate flux_core;

use flux_rs::{assert, attrs::*};

// --- exact results for `usize` ---

#[spec(fn(x: usize, y: usize) -> usize[if x < y { x } else { y }])]
fn my_min(x: usize, y: usize) -> usize {
    x.min(y)
}

#[spec(fn(x: usize, y: usize) -> usize[if x > y { x } else { y }])]
fn my_max(x: usize, y: usize) -> usize {
    x.max(y)
}

// --- concrete values ---

fn test_concrete() {
    assert(5usize.min(3) == 3);
    assert(5usize.max(3) == 5);
    assert(4usize.min(4) == 4);
    assert(4usize.max(4) == 4);
}

// --- the ordering facts callers actually rely on ---

#[spec(fn(x: usize, y: usize))]
fn test_min_is_lower_bound(x: usize, y: usize) {
    let m = x.min(y);
    assert(m <= x);
    assert(m <= y);
}

#[spec(fn(x: usize, y: usize))]
fn test_max_is_upper_bound(x: usize, y: usize) {
    let m = x.max(y);
    assert(x <= m);
    assert(y <= m);
}

// `min` returns one of its arguments.
#[spec(fn(x: usize, y: usize))]
fn test_min_is_selective(x: usize, y: usize) {
    let m = x.min(y);
    assert(m == x || m == y);
}

// --- the capacity-arithmetic shape this exists for ---

// Clamping a requested length to a capacity keeps it in bounds, so the result is a safe index
// bound for a slice of that capacity.
#[spec(fn(&[i32][@cap], n: usize) -> usize{v: v <= cap})]
fn clamp_to_capacity(buf: &[i32], n: usize) -> usize {
    n.min(buf.len())
}

// `min` under a known bound stays under it.
#[spec(fn(n: usize{n <= 100}, m: usize) -> usize{v: v <= 100})]
fn test_min_preserves_bound(n: usize, m: usize) -> usize {
    n.min(m)
}

// --- non-`usize` impls keep the vacuous default ---

// Nothing is claimed about the result, so this checks (the default is `true`, not `false`).
#[spec(fn(x: i32, y: i32) -> i32)]
fn test_i32_unconstrained(x: i32, y: i32) -> i32 {
    x.min(y)
}
