extern crate flux_core;

use std::ptr::NonNull;
use flux_rs::assert;

// --- dangling ---

pub fn test_dangling_deref_non_zst() {
    let nn = NonNull::dangling();
    unsafe {
        let _val: i32 = nn.read(); //~ ERROR refinement type error
    }
}

pub fn test_dangling_null() {
    let nn: NonNull<u32> = NonNull::dangling();
    let raw = nn.as_ptr();
    assert(raw.is_null()) //~ ERROR refinement type error
}

pub fn test_dangling_write() {
    let nn: NonNull<f32> = NonNull::dangling();
    unsafe {
        nn.write(4.2); //~ ERROR refinement type error
    }
}

pub fn test_dangling_cmp(nn: NonNull<i32>) {
    let nn_dangle = NonNull::dangling();
    assert(!(nn == nn_dangle)) //~ ERROR refinement type error
}