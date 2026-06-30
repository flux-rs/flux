extern crate flux_core;

use std::ptr::NonNull;

// new_unchecked requires a non-null pointer; passing an unconstrained pointer should fail
pub fn test_new_unchecked_null(ptr: *mut i32) {
    let _ = unsafe { NonNull::new_unchecked(ptr) }; //~ ERROR refinement type error
}

// new_unchecked with a known-null pointer should fail
pub fn test_new_unchecked_known_null() {
    let ptr: *mut i32 = std::ptr::null_mut();
    let _ = unsafe { NonNull::new_unchecked(ptr) }; //~ ERROR refinement type error
}

// new with a null pointer yields None, not Some
pub fn test_new_null_is_some() {
    use flux_rs::assert;
    let ptr: *mut i32 = std::ptr::null_mut();
    let nn = NonNull::new(ptr);
    assert(nn.is_some()); //~ ERROR refinement type error
}
