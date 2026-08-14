extern crate flux_core;
use flux_rs::assert;

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

#[flux_rs::spec(fn(target: &mut [i32][@len], n: usize{n <= len}, iter: I))]
pub fn test_take<I>(target: &mut [i32], n: usize, iter: I)
where
    I: IntoIterator<Item = i32>,
{
    let mut iter = iter.into_iter();
    let mut pushed = n;
    let to_take = target.len() - pushed;
    for element in iter.by_ref().take(to_take) {
        target[pushed] = element;
        pushed += 1;
    }
}
