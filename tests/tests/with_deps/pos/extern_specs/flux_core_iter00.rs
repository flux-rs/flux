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
