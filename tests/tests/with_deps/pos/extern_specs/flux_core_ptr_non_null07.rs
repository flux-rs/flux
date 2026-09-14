extern crate flux_core;

use flux_rs::assert;
use std::ptr::NonNull;
use std::cmp::Ordering;

// --- eq ---

#[flux::spec(fn (ptr: {NonNull<i32>[@base, @addr, @size] | addr >= base && size == 8}))]
pub fn test_ptr_eq(p: NonNull<i32>) {
    unsafe {
        let p1 = p.add(1);
        let p0 = p1.sub(1);
        assert(p.eq(&p0))
    }
}

#[flux::spec(fn (ptr: {NonNull<u64>[@base, @addr, @size] | addr >= base && size == 16}))]
pub fn test_ptr_eq_sym(p: NonNull<u64>) {
    unsafe {
        let p1 = p.add(1);
        let p0 = p1.sub(1);
        assert(p == p0)
    }
}

#[flux::spec(fn (ptr: {NonNull<u64>[@base, @addr, @size] | addr >= base && size == 16}))]
pub fn test_ptr_ne_sym(p: NonNull<u64>) {
    unsafe {
        let p1 = p.add(1);
        let p0 = p1.sub(1);
        assert(!(p != p0))
    }
}

#[flux::spec(fn(p1: NonNull<f32>[@base, @addr, @size], p2: NonNull<f32>[base, addr, size]))]
pub fn test_ptr_id_sym(p1: NonNull<f32>, p2: NonNull<f32>) {
    assert(p1 == p2)
}

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size], p2: NonNull<i32>[base, addr, size]))]
pub fn test_ptr_id(p1: NonNull<i32>, p2: NonNull<i32>) {
    assert(p1.eq(&p2))
}

#[flux::spec(fn(p1: NonNull<f32>[@base, @addr, @size],
                p2: {NonNull<f32>[@base1, addr, @size1] | base != base1 && size != size1}))]
pub fn test_ptr_id_sym_addr_only(p1: NonNull<f32>, p2: NonNull<f32>) {
    assert(p1 == p2)
}

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size],
                p2: {NonNull<i32>[@base1, addr, @size1] | base != base1 && size != size1}))]
pub fn test_ptr_id_addr_only(p1: NonNull<i32>, p2: NonNull<i32>) {
    assert(p1.eq(&p2))
}

// -- cmp --

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size],
                p2: {NonNull<i32>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr > addr1}) -> Ordering[1])]
pub fn test_ptr_cmp_gt(p1: NonNull<i32>, p2: NonNull<i32>) -> Ordering {
    p1.cmp(&p2)
}

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size],
                p2: {NonNull<i32>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr < addr1}) -> Ordering[-1])]
pub fn test_ptr_cmp_lt(p1: NonNull<i32>, p2: NonNull<i32>) -> Ordering {
    p1.cmp(&p2)
}

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size],
                p2: {NonNull<i32>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr == addr1}) -> Ordering[0])]
pub fn test_ptr_cmp_eq(p1: NonNull<i32>, p2: NonNull<i32>) -> Ordering {
    p1.cmp(&p2)
}

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size],
                p2: {NonNull<i32>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr == addr1}) -> bool[true])]
pub fn test_ptr_cmp_eq_bool(p1: NonNull<i32>, p2: NonNull<i32>) -> bool {
    p1.cmp(&p2) == Ordering::Equal
}

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size],
                p2: {NonNull<i32>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr > addr1}) -> bool[true])]
pub fn test_ptr_cmp_ne_bool(p1: NonNull<i32>, p2: NonNull<i32>) -> bool {
    p1.cmp(&p2) != Ordering::Less
}

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr <= addr1}))]
pub fn test_ptr_le_contrived<T>(p1: NonNull<T>, p2: NonNull<T>) {
    assert(p1.cmp(&p2) == Ordering::Less || p1.cmp(&p2) == Ordering::Equal)
}

// -- partial_cmp --

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size],
                p2: {NonNull<i32>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr == addr1}) -> Option<Ordering[0]>[true])]
pub fn test_ptr_partial_cmp_eq(p1: NonNull<i32>, p2: NonNull<i32>) -> Option<Ordering> {
    p1.partial_cmp(&p2)
}

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr < addr1}) -> Option<Ordering[-1]>[true])]
pub fn test_ptr_partial_cmp_lt<T>(p1: NonNull<T>, p2: NonNull<T>) -> Option<Ordering> {
    p1.partial_cmp(&p2)
}

#[flux::spec(fn(p1: NonNull<i32>[@base, @addr, @size],
                p2: {NonNull<i32>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr > addr1}) -> Option<Ordering[1]>[true])]
pub fn test_ptr_partial_cmp_gt(p1: NonNull<i32>, p2: NonNull<i32>) -> Option<Ordering> {
    p1.partial_cmp(&p2)
}

#[flux::spec(fn(p1: NonNull<i32>, p2: NonNull<i32>) -> Option<Ordering>[true])]
pub fn test_ptr_partial_cmp_opt(p1: NonNull<i32>, p2: NonNull<i32>) -> Option<Ordering> {
    p1.partial_cmp(&p2)
}

// -- lt --

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr < addr1}))]
pub fn test_ptr_lt_fn<T>(p1: NonNull<T>, p2: NonNull<T>) {
    assert(p1.lt(&p2))
}

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr < addr1}))]
pub fn test_ptr_lt<T>(p1: NonNull<T>, p2: NonNull<T>) {
    assert(p1 < p2)
}

// -- le --

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr <= addr1}))]
pub fn test_ptr_le_fn<T>(p1: NonNull<T>, p2: NonNull<T>) {
    assert(p1.le(&p2))
}

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr <= addr1}))]
pub fn test_ptr_le<T>(p1: NonNull<T>, p2: NonNull<T>) {
    assert(p1 <= p2)
}

// -- gt --

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr > addr1}))]
pub fn test_ptr_gt_fn<T>(p1: NonNull<T>, p2: NonNull<T>) {
    assert(p1.gt(&p2))
}

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr > addr1}))]
pub fn test_ptr_gt<T>(p1: NonNull<T>, p2: NonNull<T>) {
    assert(p1 > p2)
}

// -- ge --

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr >= addr1}))]
pub fn test_ptr_ge_fn<T>(p1: NonNull<T>, p2: NonNull<T>) {
    assert(p1.ge(&p2))
}

#[flux::spec(fn(p1: NonNull<T>[@base, @addr, @size],
                p2: {NonNull<T>[@base1, @addr1, @size1]
                        | base != base1 && size != size1 && addr >= addr1}))]
pub fn test_ptr_ge<T>(p1: NonNull<T>, p2: NonNull<T>) {
    assert(p1 >= p2)
}
