extern crate flux_core;

use flux_rs::assert;
use std::ptr::NonNull;
use std::cmp::Ordering;

// --- eq ---

pub fn test_ptr_neq(p: NonNull<i32>) {
    let p1 = p;
    assert(!(p1.eq(&p))) //~ ERROR refinement type error
}

#[flux::spec(fn(p1: NonNull<f64>[@base, @addr, @size], p2: NonNull<f64>[base, 8, size]))]
pub fn test_ptr_id(p1: NonNull<f64>, p2: NonNull<f64>) {
    assert(p1.eq(&p2)) //~ ERROR refinement type error
}

// --- ne ---

#[flux::spec(fn (ptr: {NonNull<u32>[@base, @addr, @size] | addr >= base && size == 8}))]
pub fn test_ptr_neq_sym(p: NonNull<u32>) {
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

// -- cmp --

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr == addr1}) -> bool[true])]
pub fn test_ptr_cmp_eq_bool<T>(p1: NonNull<T>, p2: NonNull<T>) -> bool {
    p1.cmp(&p2) != Ordering::Equal //~ ERROR refinement type error
}

// -- partial_cmp

#[flux::spec(fn(p1: NonNull<T>, p2: NonNull<T>) -> Option<Ordering>[false])]
pub fn test_ptr_partial_cmp_opt<T>(p1: NonNull<T>, p2: NonNull<T>) -> Option<Ordering> {
    p1.partial_cmp(&p2) //~ ERROR refinement type error
}

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr < addr1}) -> Option<Ordering[1]>[true])]
pub fn test_ptr_partial_cmp_lt<T>(p1: NonNull<T>, p2: NonNull<T>) -> Option<Ordering> {
    p1.partial_cmp(&p2) //~ ERROR refinement type error
}
