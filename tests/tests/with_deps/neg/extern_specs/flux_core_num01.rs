extern crate flux_core;
use flux_rs::assert;

// --- both bounded (i64 → i32): missing or incomplete checks ---

pub fn test_both_bounded_no_check(x: i64) {
    assert(i32::try_from(x).is_ok()); //~ ERROR refinement type error
}

pub fn test_both_bounded_only_lower(x: i64) {
    if x >= i32::MIN as i64 {
        assert(i32::try_from(x).is_ok()); //~ ERROR refinement type error
    }
}

pub fn test_both_bounded_only_upper(x: i64) {
    if x <= i32::MAX as i64 {
        assert(i32::try_from(x).is_ok()); //~ ERROR refinement type error
    }
}

// --- upper bounded (u64 → u32): missing check ---

pub fn test_upper_bounded_no_check(x: u64) {
    assert(u32::try_from(x).is_ok()); //~ ERROR refinement type error
}

// --- lower bounded (i64 → u64): missing check ---

pub fn test_lower_bounded_no_check(x: i64) {
    assert(u64::try_from(x).is_ok()); //~ ERROR refinement type error
}

// --- can't assert is_err unconditionally either ---

pub fn test_both_bounded_err_no_check(x: i64) {
    assert(i32::try_from(x).is_err()); //~ ERROR refinement type error
}

// --- try_into: same checks required ---

pub fn test_into_both_bounded_no_check(x: i64) {
    let r: Result<i32, _> = x.try_into();
    assert(r.is_ok()); //~ ERROR refinement type error
}

pub fn test_into_both_bounded_only_lower(x: i64) {
    if x >= i32::MIN as i64 {
        let r: Result<i32, _> = x.try_into();
        assert(r.is_ok()); //~ ERROR refinement type error
    }
}

pub fn test_into_both_bounded_only_upper(x: i64) {
    if x <= i32::MAX as i64 {
        let r: Result<i32, _> = x.try_into();
        assert(r.is_ok()); //~ ERROR refinement type error
    }
}

pub fn test_into_upper_bounded_no_check(x: u64) {
    let r: Result<u32, _> = x.try_into();
    assert(r.is_ok()); //~ ERROR refinement type error
}

pub fn test_into_lower_bounded_no_check(x: i64) {
    let r: Result<u64, _> = x.try_into();
    assert(r.is_ok()); //~ ERROR refinement type error
}
