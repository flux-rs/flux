extern crate flux_core;

use flux_rs::assert;
use std::ptr::NonNull;

// --- eq ---

pub fn test_ptr_neq(p: NonNull<i32>) {
    let p1 = p;
    assert(!(p1.eq(&p))) //~ ERROR refinement type error
}

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size], p2: NonNull<i32>[base, 0, size]))]
pub fn test_ptr_id(p1: NonNull<i32>, p2: NonNull<i32>) {
    assert(p1.eq(&p2)) //~ ERROR refinement type error
}

// --- ne ---

#[flux::spec(fn (ptr: {NonNull<i32>[@base, @addr, @size] | addr >= base && size == 8}))]
pub fn test_ptr_neq_sym(p: NonNull<i32>) {
    unsafe {
        let p1 = p.add(1);
        let p0 = p1.sub(1);
        assert(p != p0) //~ ERROR refinement type error
    }
}

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size], p2: NonNull<i32>[base, addr, size]))]
pub fn test_ptr_id_sym(p1: NonNull<i32>, p2: NonNull<i32>) {
    assert(p1 != p2) //~ ERROR refinement type error
}