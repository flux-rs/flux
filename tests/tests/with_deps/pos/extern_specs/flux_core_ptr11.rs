extern crate flux_core;

use flux_rs::assert;
use core::cmp::Ordering;

// --- eq ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_eq(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        let p0 = p1.sub(1);
        assert(p.eq(&p0))
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_eq_sym(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        let p0 = p1.sub(1);
        assert(p == p0)
    }
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, addr, @size1] i32 | base != base1 && size != size1}))]
pub fn test_ptr_id_sym_addr_only(p1: *const i32, p2: *const i32) {
    assert(p1 == p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, addr, @size1] i32 | base != base1 && size != size1}))]
pub fn test_ptr_id_addr_only(p1: *const i32, p2: *const i32) {
    assert(p1.eq(&p2))
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32, p2: *const[base, addr, size] i32))]
pub fn test_ptr_id_sym(p1: *const i32, p2: *const i32) {
    assert(p1 == p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32, p2: *const[base, addr, size] i32))]
pub fn test_ptr_id(p1: *const i32, p2: *const i32) {
    assert(p1.eq(&p2))
}

// --- lt ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_lt(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        assert(p < p1)
    }
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr < addr1}))]
pub fn test_ptr_lt_addr_only(p1: *const i32, p2: *const i32) {
    assert(p1 < p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr < addr1}))]
pub fn test_ptr_lt_addr_only_fn(p1: *const i32, p2: *const i32) {
    assert(p1.lt(&p2))
}

// --- le ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_le(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        assert(p <= p1)
    }
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr <= addr1}))]
pub fn test_ptr_le_addr_only(p1: *const i32, p2: *const i32) {
    assert(p1 <= p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr <= addr1}))]
pub fn test_ptr_le_addr_only_fn(p1: *const i32, p2: *const i32) {
    assert(p1.le(&p2))
}

// --- gt ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 40}))]
pub fn test_ptr_gt(p: *const i32) {
    unsafe {
        let p1 = p.add(4);
        assert(p1 > p)
    }
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr > addr1}))]
pub fn test_ptr_gt_addr_only(p1: *const i32, p2: *const i32) {
    assert(p1 > p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr > addr1}))]
pub fn test_ptr_gt_addr_only_fn(p1: *const i32, p2: *const i32) {
    assert(p1.ge(&p2))
}

// --- ge ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8}))]
pub fn test_ptr_ge(p: *const i32) {
    unsafe {
        let p1 = p.add(0);
        assert(p1 >= p)
    }
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr >= addr1}))]
pub fn test_ptr_ge_addr_only(p1: *const i32, p2: *const i32) {
    assert(p1 >= p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr >= addr1}))]
pub fn test_ptr_ge_addr_only_fn(p1: *const i32, p2: *const i32) {
    assert(p1.ge(&p2))
}

// -- cmp --

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr > addr1}) -> Ordering[1])]
pub fn test_ptr_cmp_gt(p1: *const i32, p2: *const i32) -> Ordering {
    p1.cmp(&p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr < addr1}) -> Ordering[-1])]
pub fn test_ptr_cmp_lt(p1: *const i32, p2: *const i32) -> Ordering {
    p1.cmp(&p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr == addr1}) -> Ordering[0])]
pub fn test_ptr_cmp_eq(p1: *const i32, p2: *const i32) -> Ordering {
    p1.cmp(&p2)
}

// -- partial_cmp --

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr == addr1}) -> Option<Ordering[0]>[true])]
pub fn test_ptr_partial_cmp_eq(p1: *const i32, p2: *const i32) -> Option<Ordering> {
    p1.partial_cmp(&p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr < addr1}) -> Option<Ordering[-1]>[true])]
pub fn test_ptr_partial_cmp_lt(p1: *const i32, p2: *const i32) -> Option<Ordering> {
    p1.partial_cmp(&p2)
}

#[flux::spec(fn(p1: *const[@base, @addr, @size] i32,
                p2: {*const[@base1, @addr1, @size1] i32
                        | base != base1 && size != size1 && addr > addr1}) -> Option<Ordering[1]>[true])]
pub fn test_ptr_partial_cmp_gt(p1: *const i32, p2: *const i32) -> Option<Ordering> {
    p1.partial_cmp(&p2)
}

#[flux::spec(fn(p1: *const i32, p2: *const i32) -> Option<Ordering>[true])]
pub fn test_ptr_partial_cmp_opt(p1: *const i32, p2: *const i32) -> Option<Ordering> {
    p1.partial_cmp(&p2)
}