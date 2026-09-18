extern crate flux_core;
use flux_rs::{assert, macros::qualifier};

// --- position ---

// If position returns Some(i), i is strictly less than the iterator's size.
pub fn test_position_in_bounds(xs: &[i32]) {
    if let Some(i) = xs.iter().position(|&x| x > 0) {
        assert(i < xs.len());
    }
}

// The bound is tight enough to use the result as a direct index.
pub fn test_position_safe_index(xs: &[i32]) {
    if let Some(i) = xs.iter().position(|&x| x > 0) {
        let _ = xs[i];
    }
}

// --- take ---

#[flux_rs::spec(fn(target: &mut [i32][100], iter: I))]
pub fn test_take_easy<I>(target: &mut [i32], iter: I)
where
    I: IntoIterator<Item = i32>,
{
    let iter = iter.into_iter();
    let mut pushed = 0;
    for element in iter.take(5) {
        // Relates `pushed` to the `Take`'s remaining count, which the `for` desugaring hides.
        qualifier!(pushed: int, k: int ; pushed + k == 5);
        target[pushed] = element;
        pushed += 1;
    }
}

#[flux_rs::spec(fn(target: &mut [i32][@len], n: usize{n <= len}, iter: I))]
pub fn test_take_loop<I>(target: &mut [i32], n: usize, iter: I)
where
    I: IntoIterator<Item = i32>,
{
    let iter = iter.into_iter();
    let mut pushed = n;
    let to_take = target.len() - pushed;
    for element in iter.take(to_take) {
        // As above, but the sum is `len` rather than a literal: `pushed` starts at `n` and
        // `to_take` is `len - n`.
        qualifier!(pushed: int, k: int, len: int ; pushed + k == len);
        target[pushed] = element;
        pushed += 1;
    }
}

// --- Take::size ---

// `Take::size` is `min(n, inner.size)`, so a position found inside a `take(3)` is bounded by
// *both* the take count and the underlying length. Each `assert` below needs a different side
// of the `min`.

pub fn test_take_position_bounded_by_count(xs: &[i32]) {
    if let Some(i) = xs.iter().take(3).position(|&x| x > 0) {
        assert(i < 3);
    }
}

pub fn test_take_position_bounded_by_len(xs: &[i32]) {
    if let Some(i) = xs.iter().take(3).position(|&x| x > 0) {
        assert(i < xs.len());
    }
}

// Taking more than the slice holds is still bounded by the slice.
pub fn test_take_beyond_end(xs: &[i32]) {
    if let Some(i) = xs.iter().take(1000).position(|&x| x > 0) {
        assert(i < xs.len());
    }
}

#[flux_rs::trusted]
#[flux_rs::spec(fn(&std::iter::Take<I>[@n, @inner]) -> usize[n])]
fn take_remaining<I>(_: &std::iter::Take<I>) -> usize {
    unimplemented!()
}

pub fn test_exhausted_take_next_preserves_remaining() {
    let xs: [i32; 0] = [];
    let mut iter = xs.iter().take(0);
    let remaining = take_remaining(&iter);
    let _ = iter.next();
    assert(take_remaining(&iter) == remaining);
    let _ = iter.next();
    assert(take_remaining(&iter) == remaining);
}

// --- Range::next ---

pub fn test_exhausted_range_is_unchanged() {
    let mut range = 0..0;
    let start = range.start;
    assert(range.next().is_none());
    assert(range.start == start);
}
