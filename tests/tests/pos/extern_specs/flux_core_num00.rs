extern crate flux_core;
use flux_rs::assert;

// --- i32 ---

pub fn test_saturating_i32() {
    let x: i32 = 5;
    let y: i32 = 10;
    let z: i32 = i32::MAX - 5;
    let w: i32 = i32::MIN + 5;
    assert(y.saturating_sub(x) == 5);
    assert(w.saturating_sub(y) == i32::MIN);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == i32::MAX);
    assert(w.saturating_add(-y) == i32::MIN);
}

pub fn test_abs_i32() {
    assert(10i32.abs() == 10);
    assert((-10i32).abs() == 10);
    assert(0i32.abs() == 0);
}

pub fn test_checked_i32() {
    assert((i32::MAX - 1).checked_add(1).is_some());
    assert(i32::MAX.checked_add(1).is_none());
    assert(i32::MIN.checked_add(-1).is_none());
    assert(5i32.checked_sub(3).is_some());
    assert(i32::MIN.checked_sub(1).is_none());
    assert(i32::MAX.checked_sub(-1).is_none());
}

pub fn test_count_i32(x: i32) {
    assert(x.count_ones() <= i32::BITS);
    assert(x.count_zeros() <= i32::BITS);
}

// --- isize ---

pub fn test_saturating_isize() {
    let x: isize = 5;
    let y: isize = 10;
    let z: isize = isize::MAX - 5;
    let w: isize = isize::MIN + 5;
    assert(y.saturating_sub(x) == 5);
    assert(w.saturating_sub(y) == isize::MIN);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == isize::MAX);
    assert(w.saturating_add(-y) == isize::MIN);
}

pub fn test_abs_isize() {
    assert(10isize.abs() == 10);
    assert((-10isize).abs() == 10);
    assert(0isize.abs() == 0);
}

pub fn test_checked_isize() {
    assert((isize::MAX - 1).checked_add(1).is_some());
    assert(isize::MAX.checked_add(1).is_none());
    assert(isize::MIN.checked_add(-1).is_none());
    assert(5isize.checked_sub(3).is_some());
    assert(isize::MIN.checked_sub(1).is_none());
    assert(isize::MAX.checked_sub(-1).is_none());
}

pub fn test_count_isize(x: isize) {
    assert(x.count_ones() <= isize::BITS);
    assert(x.count_zeros() <= isize::BITS);
}

// --- u32 ---

pub fn test_saturating_u32() {
    let x: u32 = 5;
    let y: u32 = 10;
    let z: u32 = u32::MAX - 5;
    assert(y.saturating_sub(x) == 5);
    assert(x.saturating_sub(y) == 0);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == u32::MAX);
}

pub fn test_checked_u32() {
    assert((u32::MAX - 1).checked_add(1).is_some());
    assert(u32::MAX.checked_add(1).is_none());
    assert(5u32.checked_sub(3).is_some());
    assert(0u32.checked_sub(1).is_none());
}

pub fn test_count_u32(x: u32) {
    assert(x.count_ones() <= u32::BITS);
    assert(x.count_zeros() <= u32::BITS);
}

// --- usize ---

pub fn test_saturating_usize() {
    let x: usize = 5;
    let y: usize = 10;
    let z: usize = usize::MAX - 5;
    assert(y.saturating_sub(x) == 5);
    assert(x.saturating_sub(y) == 0);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == usize::MAX);
}

pub fn test_checked_usize() {
    assert((usize::MAX - 1).checked_add(1).is_some());
    assert(usize::MAX.checked_add(1).is_none());
    assert(5usize.checked_sub(3).is_some());
    assert(0usize.checked_sub(1).is_none());
}

pub fn test_count_usize(x: usize) {
    assert(x.count_ones() <= usize::BITS);
    assert(x.count_zeros() <= usize::BITS);
}
