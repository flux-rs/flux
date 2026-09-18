extern crate flux_core;

use flux_rs::assert;

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

// --- le ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_le(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        assert(p1 <= p) //~ ERROR refinement type error
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

// --- ge ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 16}))]
pub fn test_ptr_ge(p: *const i32) {
    unsafe {
        let p1 = p.add(2);
        let p2 = p1.sub(1);
        assert(p2 >= p1) //~ ERROR refinement type error
    }
}