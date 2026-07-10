extern crate flux_core;
use flux_rs::assert;

// --- i32 ---

pub fn test_saturating_i32(x: i32, y: i32) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_checked_i32(x: i32, y: i32) {
    assert(x.checked_add(y).is_some()); //~ ERROR refinement type error
    assert(x.checked_sub(y).is_some()); //~ ERROR refinement type error
}

pub fn test_count_i32(x: i32) {
    assert(x.count_ones() == 0); //~ ERROR refinement type error
    assert(x.count_zeros() == 0); //~ ERROR refinement type error
    assert(x.leading_zeros() == 0); //~ ERROR refinement type error
    assert(x.trailing_zeros() == 0); //~ ERROR refinement type error
    assert(x.leading_ones() == 0); //~ ERROR refinement type error
    assert(x.trailing_ones() == 0); //~ ERROR refinement type error
}

pub fn test_checked_neg_i32(x: i32) {
    assert(x.checked_neg().is_some()); //~ ERROR refinement type error
}

pub fn test_checked_mul_i32(x: i32, y: i32) {
    assert(x.checked_mul(y).is_some()); //~ ERROR refinement type error
}

pub fn test_checked_div_i32(x: i32) {
    assert(x.checked_div(0).is_some()); //~ ERROR refinement type error
}

pub fn test_wrapping_i32(x: i32, y: i32) {
    assert(x.wrapping_add(y) == x + y); //~ ERROR refinement type error
    assert(x.wrapping_sub(y) == x - y); //~ ERROR refinement type error
}

// --- isize ---

pub fn test_saturating_isize(x: isize, y: isize) {
    assert(x.saturating_sub(y) == x - y); //~ ERROR refinement type error
    assert(x.saturating_add(y) == x + y); //~ ERROR refinement type error
}

pub fn test_checked_isize(x: isize, y: isize) {
    assert(x.checked_add(y).is_some()); //~ ERROR refinement type error
    assert(x.checked_sub(y).is_some()); //~ ERROR refinement type error
}

pub fn test_count_isize(x: isize) {
    assert(x.count_ones() == 0); //~ ERROR refinement type error
    assert(x.count_zeros() == 0); //~ ERROR refinement type error
    assert(x.leading_zeros() == 0); //~ ERROR refinement type error
    assert(x.trailing_zeros() == 0); //~ ERROR refinement type error
    assert(x.leading_ones() == 0); //~ ERROR refinement type error
    assert(x.trailing_ones() == 0); //~ ERROR refinement type error
}

pub fn test_checked_neg_isize(x: isize) {
    assert(x.checked_neg().is_some()); //~ ERROR refinement type error
}

pub fn test_checked_mul_isize(x: isize, y: isize) {
    assert(x.checked_mul(y).is_some()); //~ ERROR refinement type error
}

pub fn test_checked_div_isize(x: isize) {
    assert(x.checked_div(0).is_some()); //~ ERROR refinement type error
}

pub fn test_wrapping_isize(x: isize, y: isize) {
    assert(x.wrapping_add(y) == x + y); //~ ERROR refinement type error
    assert(x.wrapping_sub(y) == x - y); //~ ERROR refinement type error
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
    assert(x.leading_zeros() == 0); //~ ERROR refinement type error
    assert(x.trailing_zeros() == 0); //~ ERROR refinement type error
    assert(x.leading_ones() == 0); //~ ERROR refinement type error
    assert(x.trailing_ones() == 0); //~ ERROR refinement type error
}

pub fn test_checked_mul_u32(x: u32, y: u32) {
    assert(x.checked_mul(y).is_some()); //~ ERROR refinement type error
}

pub fn test_checked_div_u32(x: u32) {
    assert(x.checked_div(0).is_some()); //~ ERROR refinement type error
}

pub fn test_wrapping_u32(x: u32, y: u32) {
    assert(x.wrapping_add(y) == x + y); //~ ERROR refinement type error
    assert(x.wrapping_sub(y) <= x); //~ ERROR refinement type error
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
    assert(x.leading_zeros() == 0); //~ ERROR refinement type error
    assert(x.trailing_zeros() == 0); //~ ERROR refinement type error
    assert(x.leading_ones() == 0); //~ ERROR refinement type error
    assert(x.trailing_ones() == 0); //~ ERROR refinement type error
}

pub fn test_checked_mul_usize(x: usize, y: usize) {
    assert(x.checked_mul(y).is_some()); //~ ERROR refinement type error
}

pub fn test_checked_div_usize(x: usize) {
    assert(x.checked_div(0).is_some()); //~ ERROR refinement type error
}

pub fn test_wrapping_usize(x: usize, y: usize) {
    assert(x.wrapping_add(y) == x + y); //~ ERROR refinement type error
    assert(x.wrapping_sub(y) <= x); //~ ERROR refinement type error
}
