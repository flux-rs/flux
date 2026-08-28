extern crate flux_core;

#[flux_rs::trusted]
// Exposes the ghost state for transition tests. This is consistent for Windows
// values reachable through `slice::windows`, whose remaining length is nonnegative.
#[flux_rs::spec(fn(&std::slice::Windows<T>[@remaining, @size]) -> usize[remaining])]
fn windows_remaining<T>(_: &std::slice::Windows<T>) -> usize {
    unimplemented!()
}

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

pub fn test_exhausted_windows_does_not_create_false_context() {
    let xs: [i32; 0] = [];
    let mut it = xs.windows(1);
    let _ = it.next();
    let _ = windows_remaining(&it);
    let _ = xs[0]; //~ ERROR possible out-of-bounds access
}
