#![allow(invalid_null_arguments)]
extern crate flux_core;
use flux_rs::assert;
use std::ptr;

pub fn test_unknown_not_null_const(p: *const i32) {
    assert(!p.is_null()); //~ ERROR refinement type error
}

pub fn test_unknown_is_null_const(p: *const i32) {
    assert(p.is_null()); //~ ERROR refinement type error
}

pub fn test_unknown_not_null_mut(p: *mut i32) {
    assert(!p.is_null()); //~ ERROR refinement type error
}

pub fn test_unknown_is_null_mut(p: *mut i32) {
    assert(p.is_null()); //~ ERROR refinement type error
}

// --- ptr::null / ptr::null_mut ---

// null() is null, so asserting !is_null() fails
pub fn test_null_not_null() {
    let p: *const i32 = ptr::null();
    assert(!p.is_null()); //~ ERROR refinement type error
}

pub fn test_null_mut_not_null() {
    let p: *mut i32 = ptr::null_mut();
    assert(!p.is_null()); //~ ERROR refinement type error
}

// null pointer is not valid for reads
pub fn test_null_read() {
    let p: *const i32 = ptr::null();
    unsafe { let _ = std::ptr::read(p); } //~ ERROR refinement type error
}

// null pointer is not valid for writes
pub fn test_null_mut_write() {
    let p: *mut i32 = ptr::null_mut();
    unsafe { std::ptr::write(p, 42); } //~ ERROR refinement type error
}
