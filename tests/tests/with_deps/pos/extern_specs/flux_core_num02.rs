#![feature(exact_div)]
extern crate flux_core;
use flux_rs::assert;

pub fn test_unchecked_add() {
    assert(unsafe { 1i32.unchecked_add(2) } == 3);
    assert(unsafe { (i32::MAX - 1).unchecked_add(1) } == i32::MAX);
    assert(unsafe { 1u32.unchecked_add(2) } == 3);
    assert(unsafe { (u32::MAX - 1).unchecked_add(1) } == u32::MAX);
}

pub fn test_unchecked_add_after_check(x: i32, y: i32) {
    if x.checked_add(y).is_some() {
        assert(unsafe { x.unchecked_add(y) } == x + y);
    }
}

pub fn test_unchecked_sub() {
    assert(unsafe { 1i32.unchecked_sub(2) } == -1);
    assert(unsafe { (i32::MIN + 1).unchecked_sub(1) } == i32::MIN);
    assert(unsafe { 3u32.unchecked_sub(2) } == 1);
}

pub fn test_unchecked_sub_after_check(x: u32, y: u32) {
    if x >= y {
        assert(unsafe { x.unchecked_sub(y) } == x - y);
    }
}

pub fn test_unchecked_mul() {
    assert(unsafe { 3i32.unchecked_mul(-4) } == -12);
    assert(unsafe { 3u32.unchecked_mul(4) } == 12);
}

pub fn test_unchecked_mul_after_check(x: u32, y: u32) {
    if x.checked_mul(y).is_some() {
        assert(unsafe { x.unchecked_mul(y) } == x * y);
    }
}

pub fn test_unchecked_div_exact() {
    assert(unsafe { 12i32.unchecked_div_exact(4) } == 3);
    assert(unsafe { (-12i32).unchecked_div_exact(4) } == -3);
    assert(unsafe { 12i32.unchecked_div_exact(-4) } == -3);
    assert(unsafe { (-12i32).unchecked_div_exact(-4) } == 3);
    assert(unsafe { 12u32.unchecked_div_exact(4) } == 3);
}

pub fn test_unchecked_div_exact_after_check(x: u32, y: u32) {
    if y > 0 && x % y == 0 {
        unsafe { x.unchecked_div_exact(y) };
    }
}

pub fn test_unchecked_neg() {
    assert(unsafe { 5i32.unchecked_neg() } == -5);
    assert(unsafe { 0i32.unchecked_neg() } == 0);
    assert(unsafe { i32::MAX.unchecked_neg() } == i32::MIN + 1);
}

pub fn test_unchecked_neg_after_check(x: i32) {
    if x > i32::MIN {
        assert(unsafe { x.unchecked_neg() } == -x);
    }
}
