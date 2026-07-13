extern crate flux_core;

use std::ptr::NonNull;

// --- read ---

// unconstrained NonNull: can't prove valid or aligned
pub fn test_read(nn: NonNull<i32>) -> i32 {
    unsafe { nn.read() } //~ ERROR refinement type error
                         //~| ERROR refinement type error
}

// --- write ---

// unconstrained NonNull: can't prove valid or aligned
pub fn test_write(nn: NonNull<i32>, val: i32) {
    unsafe { nn.write(val) } //~ ERROR refinement type error
                              //~| ERROR refinement type error
}

