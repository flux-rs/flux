extern crate flux_core;
use flux_rs::assert;

// --- i32 ---

pub fn test_saturating_i32(x: i32, y: i32) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_abs_i32(x: i32) {
    let _y = x.abs(); //~ ERROR refinement type
}

pub fn test_checked_i32(x: i32, y: i32) {
    assert(x.checked_add(y).is_some()); //~ ERROR refinement type error
    assert(x.checked_sub(y).is_some()); //~ ERROR refinement type error
}

pub fn test_count_i32(x: i32) {
    assert(x.count_ones() == 0); //~ ERROR refinement type error
    assert(x.count_zeros() == 0); //~ ERROR refinement type error
}

// --- isize ---

pub fn test_saturating_isize(x: isize, y: isize) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_abs_isize(x: isize) {
    let _y = x.abs(); //~ ERROR refinement type
}

pub fn test_checked_isize(x: isize, y: isize) {
    assert(x.checked_add(y).is_some()); //~ ERROR refinement type error
    assert(x.checked_sub(y).is_some()); //~ ERROR refinement type error
}

pub fn test_count_isize(x: isize) {
    assert(x.count_ones() == 0); //~ ERROR refinement type error
    assert(x.count_zeros() == 0); //~ ERROR refinement type error
}

// --- u32 ---

pub fn test_saturating_u32(x: u32, y: u32) {
    let sub = x - y; //~ ERROR arithmetic operation may underflow
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_checked_u32(x: u32, y: u32) {
    assert(x.checked_add(y).is_some()); //~ ERROR refinement type error
    assert(x.checked_sub(y).is_some()); //~ ERROR refinement type error
}

pub fn test_count_u32(x: u32) {
    assert(x.count_ones() == 0); //~ ERROR refinement type error
    assert(x.count_zeros() == 0); //~ ERROR refinement type error
}

// --- usize ---

pub fn test_saturating_usize(x: usize, y: usize) {
    let sub = x - y; //~ ERROR arithmetic operation may underflow
    assert(x.saturating_sub(y) == sub); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_checked_usize(x: usize, y: usize) {
    assert(x.checked_add(y).is_some()); //~ ERROR refinement type error
    assert(x.checked_sub(y).is_some()); //~ ERROR refinement type error
}

pub fn test_count_usize(x: usize) {
    assert(x.count_ones() == 0); //~ ERROR refinement type error
    assert(x.count_zeros() == 0); //~ ERROR refinement type error
}
