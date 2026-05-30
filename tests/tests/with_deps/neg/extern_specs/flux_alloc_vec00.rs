use flux_rs::{assert, attrs::*};

extern crate flux_alloc;
extern crate flux_core;

// The element refinement must not be fabricated when the input `Vec` carries none, even
// though indexing now preserves the element refinement (see flux_alloc_vec00.rs in pos/).
fn test(v: Vec<i32>) {
    if v.len() > 0 {
        let y = v[0];
        assert(y > 0); //~ ERROR refinement type
    }
}
