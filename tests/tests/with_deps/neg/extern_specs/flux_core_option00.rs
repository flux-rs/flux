extern crate flux_core;
use flux_rs::assert;

// --- expect ---

pub fn test_expect(x: Option<i32>) {
    let _ = x.expect("oops"); //~ ERROR refinement type error
}

// --- and ---

pub fn test_and(x: Option<i32>, y: Option<i32>) {
    assert(x.and(y).is_some()); //~ ERROR refinement type error
}

// --- or ---

pub fn test_or(x: Option<i32>, y: Option<i32>) {
    assert(x.or(y).is_none()); //~ ERROR refinement type error
}

// --- map ---

pub fn test_map(x: Option<i32>) {
    assert(x.map(|v| v + 1).is_some()); //~ ERROR refinement type error
}

// --- take ---

pub fn test_take_result_always_some(x: Option<i32>) {
    let mut x = x;
    assert(x.take().is_some()); //~ ERROR refinement type error
}

pub fn test_take_self_still_some(mut x: Option<i32>) {
    let _ = x.take();
    assert(x.is_some()); //~ ERROR refinement type error
}

// --- replace ---

pub fn test_replace_result_always_some(x: Option<i32>) {
    let mut x = x;
    assert(x.replace(1).is_some()); //~ ERROR refinement type error
}

pub fn test_replace_self_still_none(mut x: Option<i32>) {
    let _ = x.replace(1);
    assert(x.is_none()); //~ ERROR refinement type error
}

// --- ok_or ---

pub fn test_ok_or(x: Option<i32>) {
    assert(x.ok_or("err").is_ok()); //~ ERROR refinement type error
}

// --- ok_or_else ---

pub fn test_ok_or_else(x: Option<i32>) {
    assert(x.ok_or_else(|| "err").is_ok()); //~ ERROR refinement type error
}

// --- and_then ---

pub fn test_and_then(x: Option<i32>) {
    assert(x.and_then(|v| Some(v + 1)).is_some()); //~ ERROR refinement type error
}
