extern crate flux_core;

// windows() yields slices of length window_size, so indexing out of that
// range is a statically detectable error.

pub fn test_windows_oob(xs: &[i32]) {
    let mut it = xs.windows(2);
    if let Some(w) = it.next() {
        let _ = w[2]; //~ ERROR possible out-of-bounds access
    }
}

pub fn test_windows_unwrap_unchecked(xs: &[i32]) {
    let _ = xs.windows(2).next().unwrap(); //~ ERROR refinement type error
}
