extern crate flux_core;

use flux_rs::assert;

// --- eq ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 8 && addr % 4 == 0}))]
pub fn test_ptr_eq(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        let p0 = p1.sub(1);
        assert(p.eq(&p0))
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 8 && addr % 4 == 0}))]
pub fn test_ptr_eq_sym(p: *const i32) {
    unsafe {
        let p1 = p.add(1);
        let p0 = p1.sub(1);
        assert(p == p0)
    }
}

#[flux::spec(fn(
    p1: *const[@base, @addr, @size] i32,
    p2: { *const[@b, @a, @s] i32 | b == base && a == addr && s == size }
))]
pub fn test_ptr_id(p1: *const i32, p2: *const i32) {
    assert(p1 == p2)
}