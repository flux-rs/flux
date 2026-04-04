extern crate flux_core;
use flux_rs::assert;

// --- signed ---

pub fn test_saturating_i8() {
    let x: i8 = 5;
    let y: i8 = 10;
    let z: i8 = i8::MAX - 5;
    let w: i8 = i8::MIN + 5;
    assert(y.saturating_sub(x) == 5);
    assert(w.saturating_sub(y) == i8::MIN);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == i8::MAX);
    assert(w.saturating_add(-y) == i8::MIN);
}

pub fn test_abs_i8() {
    assert(10i8.abs() == 10);
    assert((-10i8).abs() == 10);
    assert(0i8.abs() == 0);
}

pub fn test_saturating_i16() {
    let x: i16 = 5;
    let y: i16 = 10;
    let z: i16 = i16::MAX - 5;
    let w: i16 = i16::MIN + 5;
    assert(y.saturating_sub(x) == 5);
    assert(w.saturating_sub(y) == i16::MIN);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == i16::MAX);
    assert(w.saturating_add(-y) == i16::MIN);
}

pub fn test_abs_i16() {
    assert(10i16.abs() == 10);
    assert((-10i16).abs() == 10);
    assert(0i16.abs() == 0);
}

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

pub fn test_saturating_i64() {
    let x: i64 = 5;
    let y: i64 = 10;
    let z: i64 = i64::MAX - 5;
    let w: i64 = i64::MIN + 5;
    assert(y.saturating_sub(x) == 5);
    assert(w.saturating_sub(y) == i64::MIN);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == i64::MAX);
    assert(w.saturating_add(-y) == i64::MIN);
}

pub fn test_abs_i64() {
    assert(10i64.abs() == 10);
    assert((-10i64).abs() == 10);
    assert(0i64.abs() == 0);
}

pub fn test_saturating_i128() {
    let x: i128 = 5;
    let y: i128 = 10;
    let z: i128 = i128::MAX - 5;
    let w: i128 = i128::MIN + 5;
    assert(y.saturating_sub(x) == 5);
    assert(w.saturating_sub(y) == i128::MIN);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == i128::MAX);
    assert(w.saturating_add(-y) == i128::MIN);
}

pub fn test_abs_i128() {
    assert(10i128.abs() == 10);
    assert((-10i128).abs() == 10);
    assert(0i128.abs() == 0);
}

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

// --- unsigned ---

pub fn test_saturating_u8() {
    let x: u8 = 5;
    let y: u8 = 10;
    let z: u8 = u8::MAX - 5;
    assert(y.saturating_sub(x) == 5);
    assert(x.saturating_sub(y) == 0);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == u8::MAX);
}

pub fn test_saturating_u16() {
    let x: u16 = 5;
    let y: u16 = 10;
    let z: u16 = u16::MAX - 5;
    assert(y.saturating_sub(x) == 5);
    assert(x.saturating_sub(y) == 0);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == u16::MAX);
}

pub fn test_saturating_u32() {
    let x: u32 = 5;
    let y: u32 = 10;
    let z: u32 = u32::MAX - 5;
    assert(y.saturating_sub(x) == 5);
    assert(x.saturating_sub(y) == 0);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == u32::MAX);
}

pub fn test_saturating_u64() {
    let x: u64 = 5;
    let y: u64 = 10;
    let z: u64 = u64::MAX - 5;
    assert(y.saturating_sub(x) == 5);
    assert(x.saturating_sub(y) == 0);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == u64::MAX);
}

pub fn test_saturating_u128() {
    let x: u128 = 5;
    let y: u128 = 10;
    let z: u128 = u128::MAX - 5;
    assert(y.saturating_sub(x) == 5);
    assert(x.saturating_sub(y) == 0);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == u128::MAX);
}

pub fn test_saturating_usize() {
    let x: usize = 5;
    let y: usize = 10;
    let z: usize = usize::MAX - 5;
    assert(y.saturating_sub(x) == 5);
    assert(x.saturating_sub(y) == 0);
    assert(x.saturating_add(y) == 15);
    assert(z.saturating_add(y) == usize::MAX);
}
