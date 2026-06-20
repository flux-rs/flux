extern crate flux_core;
use flux_rs::assert;

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
