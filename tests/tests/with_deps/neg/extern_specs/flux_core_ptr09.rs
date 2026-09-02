extern crate flux_core;

use std::ptr;
use flux_rs::assert;

// --- dangling ---

pub fn test_dangling_deref_non_zst() {
    let p: *const i32 = ptr::dangling();
    unsafe {
        let _val = p.read(); //~ ERROR refinement type error
    }
}

// this and the NonNull version of dangling() never return null
pub fn test_dangling_null() {
    let p: *const i64 = ptr::dangling();
    assert(p.is_null()) //~ ERROR refinement type error
}

// in reality, dangling() always returns the alignment of the underlying
// type; however, it is only specified to return an aligned pointer, so
// comparisons may be unequal
pub fn test_dangling_same() {
    let p1: *const u64 = ptr::dangling();
    let p2: *const u64 = ptr::dangling();
    assert(p1 == p2) //~ ERROR refinement type error
}

// --- dangling_mut ---

pub fn test_dangling_write() {
    let p: *mut f32 = ptr::dangling_mut();
    unsafe {
        p.write(12.3); //~ ERROR refinement type error
    }
}

pub fn test_dangling_cmp(p: *mut i32) {
    let p_dangle: *mut i32 = ptr::dangling_mut();
    assert(!(p == p_dangle)) //~ ERROR refinement type error
}

pub fn test_dangling_aligned() {
    let p: *mut u64 = ptr::dangling_mut();
    assert(!p.is_aligned()) //~ ERROR refinement type error
}