extern crate flux_core;

use std::ptr;
use flux_rs::assert;

// --- dangling ---

pub fn test_dangling_deref_zst() {
    let p: *const () = ptr::dangling();
    unsafe {
        let _val: () = p.read();
    }
}

// --- dangling_mut ---

pub fn test_dangling_not_null() {
    let p: *mut i32 = ptr::dangling_mut();
    assert(!p.is_null())
}