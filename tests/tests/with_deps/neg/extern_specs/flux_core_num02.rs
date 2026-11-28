#![feature(exact_div)]
extern crate flux_core;

pub fn test_unchecked_add(x: i32, y: i32) {
    unsafe { x.unchecked_add(y) }; //~ ERROR refinement type error
                                   //~| ERROR refinement type error
}

pub fn test_unchecked_add_overflow() {
    unsafe { u8::MAX.unchecked_add(1) }; //~ ERROR refinement type error
}

pub fn test_unchecked_sub(x: u32, y: u32) {
    unsafe { x.unchecked_sub(y) }; //~ ERROR refinement type error
}

pub fn test_unchecked_sub_overflow() {
    unsafe { i32::MIN.unchecked_sub(1) }; //~ ERROR refinement type error
}

pub fn test_unchecked_mul(x: u32, y: u32) {
    unsafe { x.unchecked_mul(y) }; //~ ERROR refinement type error
}

pub fn test_unchecked_mul_overflow() {
    unsafe { i8::MIN.unchecked_mul(-1) }; //~ ERROR refinement type error
}

pub fn test_unchecked_div_exact_zero(x: u32) {
    unsafe { x.unchecked_div_exact(0) }; //~ ERROR refinement type error
}

pub fn test_unchecked_div_exact_remainder() {
    unsafe { 7i32.unchecked_div_exact(2) }; //~ ERROR refinement type error
}

pub fn test_unchecked_div_exact_overflow() {
    unsafe { i32::MIN.unchecked_div_exact(-1) }; //~ ERROR refinement type error
}

pub fn test_unchecked_neg(x: i32) {
    unsafe { x.unchecked_neg() }; //~ ERROR refinement type error
}

pub fn test_unchecked_neg_min() {
    unsafe { i64::MIN.unchecked_neg() }; //~ ERROR refinement type error
}
