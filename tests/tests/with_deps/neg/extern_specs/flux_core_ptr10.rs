extern crate flux_core;

use flux_rs::assert;

// --- eq ---

pub fn test_ptr_neq(p: *mut i32) {
    let p1 = p;
    assert(!(p1.eq(&p))) //~ ERROR refinement type error
}