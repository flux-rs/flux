extern crate flux_core;
use flux_rs::assert;

// --- windows ---

pub fn test_windows_some_concrete() {
    let v = [1, 2, 3, 4, 5];
    let mut it = v.windows(3);
    assert(it.next().is_some());
}

pub fn test_windows_none_when_too_short() {
    let v: [i32; 2] = [1, 2];
    let mut it = v.windows(3);
    assert(it.next().is_none());
}

pub fn test_windows_some_branch(xs: &[i32]) {
    if xs.len() >= 4 {
        let mut it = xs.windows(4);
        assert(it.next().is_some());
    }
}

pub fn test_windows_none_branch(xs: &[i32]) {
    if xs.len() < 4 {
        let mut it = xs.windows(4);
        assert(it.next().is_none());
    }
}

// The key property: window_size is tracked in the item type.
// Flux knows w has length 2, so w[0] and w[1] are provably safe without a runtime check.
pub fn test_windows_index_safe(xs: &[i32]) {
    let mut it = xs.windows(2);
    if let Some(w) = it.next() {
        let _diff = w[1] - w[0];
    }
}

// Same with window_size=3: w[0], w[1], w[2] are all provably safe.
pub fn test_windows_index_safe_3(xs: &[i32]) {
    let mut it = xs.windows(3);
    if let Some(w) = it.next() {
        let _ = w[0];
        let _ = w[1];
        let _ = w[2];
    }
}
