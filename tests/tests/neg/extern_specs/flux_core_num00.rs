extern crate flux_core;
use flux_rs::assert;

// --- signed ---

pub fn test_saturating_i8(x: i8, y: i8) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_abs_i8(x: i8) {
    let _y = x.abs(); //~ ERROR refinement type
}

pub fn test_saturating_i16(x: i16, y: i16) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_abs_i16(x: i16) {
    let _y = x.abs(); //~ ERROR refinement type
}

pub fn test_saturating_i32(x: i32, y: i32) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_abs_i32(x: i32) {
    let _y = x.abs(); //~ ERROR refinement type
}

pub fn test_saturating_i64(x: i64, y: i64) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_abs_i64(x: i64) {
    let _y = x.abs(); //~ ERROR refinement type
}

pub fn test_saturating_i128(x: i128, y: i128) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_abs_i128(x: i128) {
    let _y = x.abs(); //~ ERROR refinement type
}

pub fn test_saturating_isize(x: isize, y: isize) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_abs_isize(x: isize) {
    let _y = x.abs(); //~ ERROR refinement type
}

// --- unsigned ---

pub fn test_saturating_u8(x: u8, y: u8) {
    let sub = x - y; //~ ERROR arithmetic operation may underflow
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_saturating_u16(x: u16, y: u16) {
    let sub = x - y; //~ ERROR arithmetic operation may underflow
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_saturating_u32(x: u32, y: u32) {
    let sub = x - y; //~ ERROR arithmetic operation may underflow
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_saturating_u64(x: u64, y: u64) {
    let sub = x - y; //~ ERROR arithmetic operation may underflow
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_saturating_u128(x: u128, y: u128) {
    let sub = x - y; //~ ERROR arithmetic operation may underflow
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_saturating_usize(x: usize, y: usize) {
    let sub = x - y; //~ ERROR arithmetic operation may underflow
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}
