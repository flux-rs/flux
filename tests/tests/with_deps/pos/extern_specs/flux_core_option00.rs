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

// --- take ---

pub fn test_take_some() {
    let mut x: Option<i32> = Some(1);
    assert(x.take().is_some());
    assert(x.is_none());
}

pub fn test_take_none() {
    let mut x: Option<i32> = None;
    assert(x.take().is_none());
    assert(x.is_none());
}

pub fn test_take_return_matches_original(x: Option<i32>) {
    let mut x = x;
    let was_some = x.is_some();
    let result = x.take();
    assert(result.is_some() == was_some);
    assert(x.is_none());
}

// --- replace ---

pub fn test_replace_leaves_some() {
    let mut x: Option<i32> = None;
    let _ = x.replace(1);
    assert(x.is_some());
}

pub fn test_replace_returns_old_none() {
    let mut x: Option<i32> = None;
    assert(x.replace(1).is_none());
}

pub fn test_replace_returns_old_some() {
    let mut x: Option<i32> = Some(0);
    assert(x.replace(1).is_some());
}

pub fn test_replace_return_matches_original(x: Option<i32>) {
    let mut x = x;
    let was_some = x.is_some();
    let result = x.replace(42);
    assert(result.is_some() == was_some);
    assert(x.is_some());
}

// --- ok_or ---

pub fn test_ok_or_some() {
    let x: Option<i32> = Some(1);
    assert(x.ok_or("err").is_ok());
}

pub fn test_ok_or_none() {
    let x: Option<i32> = None;
    assert(x.ok_or("err").is_err());
}

pub fn test_ok_or_branch(x: Option<i32>) {
    assert(x.ok_or("err").is_ok() == x.is_some());
}

// --- ok_or_else ---

pub fn test_ok_or_else_some() {
    let x: Option<i32> = Some(1);
    assert(x.ok_or_else(|| "err").is_ok());
}

pub fn test_ok_or_else_branch(x: Option<i32>) {
    assert(x.ok_or_else(|| "err").is_ok() == x.is_some());
}

// --- and_then ---

pub fn test_and_then_none_propagates(x: Option<i32>) {
    let result = x.and_then(|v| if v > 0 { Some(v) } else { None });
    if x.is_none() {
        assert(result.is_none());
    }
}

pub fn test_and_then_none_input() {
    let x: Option<i32> = None;
    assert(x.and_then(|v| Some(v + 1)).is_none());
}
