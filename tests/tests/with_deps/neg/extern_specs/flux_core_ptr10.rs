extern crate flux_core;

use flux_rs::assert;
use std::cmp::Ordering;

// --- eq ---

pub fn test_ptr_neq(p: *mut i32) {
    let p1 = p;
    assert(!(p1.eq(&p))) //~ ERROR refinement type error
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32, p2: *const[base, 0, size] i32))]
pub fn test_ptr_id(p1: *const i32, p2: *const i32) {
    assert(p1.eq(&p2)) //~ ERROR refinement type error
}

// --- ne ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_neq_sym(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        let p0 = p1.sub(1);
        assert(p != p0) //~ ERROR refinement type error
    }
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32, p2: *const[base, addr, size] i32))]
pub fn test_ptr_id_sym(p1: *const i32, p2: *const i32) {
    assert(p1 != p2) //~ ERROR refinement type error
}

// --- lt ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_lt(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        assert(p1 < p) //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_lt_fn(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        assert(p1.lt(&p)) //~ ERROR refinement type error
    }
}

// --- le ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_le(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        assert(p1 <= p) //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_le_fn(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        assert(p1.le(&p)) //~ ERROR refinement type error
    }
}

// --- gt ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 40}))]
pub fn test_ptr_gt(p: *const i32) {
    unsafe {
        let p1 = p.add(4);
        assert(p > p1) //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 40}))]
pub fn test_ptr_gt_fn(p: *const i32) {
    unsafe {
        let p1 = p.add(4);
        assert(p.gt(&p1)) //~ ERROR refinement type error
    }
}

// --- ge ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 16}))]
pub fn test_ptr_ge(p: *const i32) {
    unsafe {
        let p1 = p.add(2);
        let p2 = p1.sub(1);
        assert(p2 >= p1) //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 16}))]
pub fn test_ptr_ge_fn(p: *const i32) {
    unsafe {
        let p1 = p.add(2);
        let p2 = p1.sub(1);
        assert(p2.ge(&p1)) //~ ERROR refinement type error
    }
}

// -- cmp --

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr == addr1}) -> bool[true])]
pub fn test_ptr_cmp_eq_bool(p1: *const i32, p2: *const i32) -> bool {
    p1.cmp(&p2) != Ordering::Equal //~ ERROR refinement type error
}

// -- partial_cmp

#[flux::spec(fn(p1: *const i32, p2: *const i32) -> Option<Ordering>[false])]
pub fn test_ptr_partial_cmp_opt(p1: *const i32, p2: *const i32) -> Option<Ordering> {
    p1.partial_cmp(&p2) //~ ERROR refinement type error
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr < addr1}) -> Option<Ordering[1]>[true])]
pub fn test_ptr_partial_cmp_lt(p1: *const i32, p2: *const i32) -> Option<Ordering> {
    p1.partial_cmp(&p2) //~ ERROR refinement type error
}
