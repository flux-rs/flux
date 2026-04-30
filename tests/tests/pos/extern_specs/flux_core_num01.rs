extern crate flux_core;
use flux_rs::assert;

// --- both bounded: signed → narrower signed (i64 → i32) ---

pub fn test_both_bounded_ok(x: i64) {
    if x >= i32::MIN as i64 && x <= i32::MAX as i64 {
        assert(i32::try_from(x).is_ok());
    }
}

pub fn test_both_bounded_err_low(x: i64) {
    if x < i32::MIN as i64 {
        assert(i32::try_from(x).is_err());
    }
}

pub fn test_both_bounded_err_high(x: i64) {
    if x > i32::MAX as i64 {
        assert(i32::try_from(x).is_err());
    }
}

pub fn test_both_bounded_concrete() {
    assert(i32::try_from(42i64).is_ok());
    assert(i32::try_from(42i64).unwrap() == 42);
    assert(i32::try_from(-42i64).unwrap() == -42);
    assert(i32::try_from(i32::MAX as i64).unwrap() == i32::MAX);
    assert(i32::try_from(i32::MIN as i64).unwrap() == i32::MIN);
    assert(i32::try_from((i32::MAX as i64) + 1).is_err());
    assert(i32::try_from((i32::MIN as i64) - 1).is_err());
}

// --- both bounded: signed → unsigned narrowing (i32 → u8) ---

pub fn test_both_bounded_su_ok(x: i32) {
    if x >= 0 && x <= u8::MAX as i32 {
        assert(u8::try_from(x).is_ok());
    }
}

pub fn test_both_bounded_su_err_neg(x: i32) {
    if x < 0 {
        assert(u8::try_from(x).is_err());
    }
}

pub fn test_both_bounded_su_err_high(x: i32) {
    if x > u8::MAX as i32 {
        assert(u8::try_from(x).is_err());
    }
}

// --- upper bounded: unsigned → unsigned narrowing (u64 → u32) ---

pub fn test_upper_bounded_u_ok(x: u64) {
    if x <= u32::MAX as u64 {
        assert(u32::try_from(x).is_ok());
    }
}

pub fn test_upper_bounded_u_err(x: u64) {
    if x > u32::MAX as u64 {
        assert(u32::try_from(x).is_err());
    }
}

pub fn test_upper_bounded_u_concrete() {
    assert(u32::try_from(1000u64).is_ok());
    assert(u32::try_from(1000u64).unwrap() == 1000u32);
    assert(u32::try_from((u32::MAX as u64) + 1).is_err());
}

// --- upper bounded: unsigned → signed (u64 → i64) ---

pub fn test_upper_bounded_us_ok(x: u64) {
    if x <= i64::MAX as u64 {
        assert(i64::try_from(x).is_ok());
    }
}

pub fn test_upper_bounded_us_err(x: u64) {
    if x > i64::MAX as u64 {
        assert(i64::try_from(x).is_err());
    }
}

// --- lower bounded: signed → unsigned same width (i64 → u64) ---

pub fn test_lower_bounded_ok(x: i64) {
    if x >= 0 {
        assert(u64::try_from(x).is_ok());
    }
}

pub fn test_lower_bounded_err(x: i64) {
    if x < 0 {
        assert(u64::try_from(x).is_err());
    }
}

pub fn test_lower_bounded_concrete() {
    assert(u64::try_from(100i64).is_ok());
    assert(u64::try_from(100i64).unwrap() == 100u64);
    assert(u64::try_from(-1i64).is_err());
}

// --- try_into mirrors ---

// both bounded: i64 → i32
pub fn test_into_both_bounded_ok(x: i64) {
    if x >= i32::MIN as i64 && x <= i32::MAX as i64 {
        let r: Result<i32, _> = x.try_into();
        assert(r.is_ok());
    }
}

pub fn test_into_both_bounded_err_low(x: i64) {
    if x < i32::MIN as i64 {
        let r: Result<i32, _> = x.try_into();
        assert(r.is_err());
    }
}

pub fn test_into_both_bounded_err_high(x: i64) {
    if x > i32::MAX as i64 {
        let r: Result<i32, _> = x.try_into();
        assert(r.is_err());
    }
}

pub fn test_into_both_bounded_concrete() {
    let r: Result<i32, _> = 42i64.try_into();
    assert(r.is_ok());
    assert(r.unwrap() == 42);
    let r: Result<i32, _> = (-42i64).try_into();
    assert(r.unwrap() == -42);
    let r: Result<i32, _> = ((i32::MAX as i64) + 1).try_into();
    assert(r.is_err());
    let r: Result<i32, _> = ((i32::MIN as i64) - 1).try_into();
    assert(r.is_err());
}

// upper bounded: u64 → u32
pub fn test_into_upper_bounded_ok(x: u64) {
    if x <= u32::MAX as u64 {
        let r: Result<u32, _> = x.try_into();
        assert(r.is_ok());
    }
}

pub fn test_into_upper_bounded_err(x: u64) {
    if x > u32::MAX as u64 {
        let r: Result<u32, _> = x.try_into();
        assert(r.is_err());
    }
}

// lower bounded: i64 → u64
pub fn test_into_lower_bounded_ok(x: i64) {
    if x >= 0 {
        let r: Result<u64, _> = x.try_into();
        assert(r.is_ok());
    }
}

pub fn test_into_lower_bounded_err(x: i64) {
    if x < 0 {
        let r: Result<u64, _> = x.try_into();
        assert(r.is_err());
    }
}
