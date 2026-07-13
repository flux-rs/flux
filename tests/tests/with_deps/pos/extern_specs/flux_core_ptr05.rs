extern crate flux_core;
use flux_rs::assert;
use std::ptr;

// --- *const T::is_null ---

pub fn test_is_null_branch_const(p: *const i32) {
    if p.is_null() {
        assert(p.is_null());
    }
}

#[flux::spec(fn (p: {*const[@base, @addr, @size] i32 | addr > 0}))]
pub fn test_not_null_const(p: *const i32) {
    assert(!p.is_null());
}

#[flux::spec(fn (p: {*const[@base, @addr, @size] i32 | addr == 0}))]
pub fn test_null_const(p: *const i32) {
    assert(p.is_null());
}

// --- *mut T::is_null ---

pub fn test_is_null_branch_mut(p: *mut i32) {
    if p.is_null() {
        assert(p.is_null());
    }
}

#[flux::spec(fn (p: {*mut[@base, @addr, @size] i32 | addr > 0}))]
pub fn test_not_null_mut(p: *mut i32) {
    assert(!p.is_null());
}

#[flux::spec(fn (p: {*mut[@base, @addr, @size] i32 | addr == 0}))]
pub fn test_null_mut(p: *mut i32) {
    assert(p.is_null());
}

// --- ptr::null / ptr::null_mut ---

pub fn test_null_is_null() {
    let p: *const i32 = ptr::null();
    assert(p.is_null());
}

pub fn test_null_mut_is_null() {
    let p: *mut i32 = ptr::null_mut();
    assert(p.is_null());
}
