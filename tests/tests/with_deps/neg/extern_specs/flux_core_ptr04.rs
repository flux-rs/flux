extern crate flux_core;

// --- read_unaligned ---

// No preconditions on the pointer — validity cannot be verified
pub fn test_read_unaligned_invalid(ptr: *const i32) -> i32 {
    unsafe { std::ptr::read_unaligned(ptr) } //~ ERROR refinement type error
}

// --- write_unaligned ---

pub fn test_write_unaligned_invalid(ptr: *mut i32, val: i32) {
    unsafe { std::ptr::write_unaligned(ptr, val) } //~ ERROR refinement type error
}
