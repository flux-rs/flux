extern crate flux_core;

use std::ptr::NonNull;

// Non-zero offsets still require the pointer to be in bounds.
pub fn test_nonnull_nonzero_offset() {
    let p = NonNull::<u64>::dangling();
    let _a = unsafe { p.add(1) }; //~ ERROR refinement type error
}

pub fn test_raw_nonzero_offset(p: *const u64) {
    let _a = unsafe { p.add(1) }; //~ ERROR refinement type error
}
