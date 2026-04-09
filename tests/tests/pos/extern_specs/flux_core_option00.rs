extern crate flux_core;
use flux_rs::assert;

// --- expect ---

pub fn test_expect() {
    let x: Option<i32> = Some(1);
    let _ = x.expect("should be some");
}

pub fn test_expect_after_check(x: Option<i32>) {
    if x.is_some() {
        let _ = x.expect("should be some");
    }
}

// --- unwrap_or ---

pub fn test_unwrap_or(x: Option<i32>) {
    let _ = x.unwrap_or(0);
}

// --- unwrap_or_else ---

pub fn test_unwrap_or_else(x: Option<i32>) {
    let _ = x.unwrap_or_else(|| 0);
}

// --- and ---

pub fn test_and_none_left(x: Option<i32>) {
    assert(x.and(Some(1)).is_some() == x.is_some());
}

pub fn test_and_none_right(x: Option<i32>) {
    let n: Option<i32> = None;
    assert(x.and(n).is_none());
}

pub fn test_and_both_some() {
    let a: Option<i32> = Some(1);
    let b: Option<i32> = Some(2);
    assert(a.and(b).is_some());
}

// --- or ---

pub fn test_or_some_left() {
    let a: Option<i32> = Some(1);
    let b: Option<i32> = None;
    assert(a.or(b).is_some());
}

pub fn test_or_some_right(x: Option<i32>) {
    assert(x.or(Some(0)).is_some());
}

pub fn test_or_both_none() {
    let a: Option<i32> = None;
    let b: Option<i32> = None;
    assert(a.or(b).is_none());
}

// --- map ---

pub fn test_map_preserves_some() {
    let x: Option<i32> = Some(1);
    assert(x.map(|v| v + 1).is_some());
}

pub fn test_map_preserves_none() {
    let x: Option<i32> = None;
    assert(x.map(|v| v + 1).is_none());
}

pub fn test_map_branch(x: Option<i32>) {
    assert(x.map(|v| v + 1).is_some() == x.is_some());
}

// --- map_or ---

pub fn test_map_or_branch(x: Option<i32>) {
    let _ = x.map_or(0, |v| v + 1);
}
