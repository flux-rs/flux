extern crate flux_core;
use flux_rs::assert;

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
