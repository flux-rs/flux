extern crate flux_core;
use flux_rs::assert;

// --- is_ok / is_err ---

pub fn test_is_ok_err() {
    let ok: Result<i32, &str> = Ok(5);
    let err: Result<i32, &str> = Err("oops");
    assert(ok.is_ok());
    assert(!ok.is_err());
    assert(err.is_err());
    assert(!err.is_ok());
}

pub fn test_is_ok_after_branch(r: Result<i32, &str>) {
    if r.is_ok() {
        assert(r.is_ok());
    } else {
        assert(r.is_err());
    }
}

// --- ok / err ---

pub fn test_ok() {
    let ok: Result<i32, &str> = Ok(5);
    let err: Result<i32, &str> = Err("oops");
    assert(ok.ok().is_some());
    assert(err.ok().is_none());
}

pub fn test_err() {
    let ok: Result<i32, &str> = Ok(5);
    let err: Result<i32, &str> = Err("oops");
    assert(ok.err().is_none());
    assert(err.err().is_some());
}

pub fn test_ok_err_branch(r: Result<i32, &str>) {
    if r.is_ok() {
        assert(r.ok().is_some());
        assert(r.err().is_none());
    } else {
        assert(r.ok().is_none());
        assert(r.err().is_some());
    }
}

// --- as_ref / as_mut ---

pub fn test_as_ref(r: Result<i32, &str>) {
    assert(r.as_ref().is_ok() == r.is_ok());
}

pub fn test_as_mut(mut r: Result<i32, &str>) {
    assert(r.as_mut().is_ok() == r.is_ok());
}

// --- map / map_err ---

pub fn test_map() {
    let ok: Result<i32, &str> = Ok(5);
    let err: Result<i32, &str> = Err("oops");
    assert(ok.map(|x| x + 1).is_ok());
    assert(err.map(|x| x + 1).is_err());
}

pub fn test_map_preserves_ok(r: Result<i32, &str>) {
    let mapped = r.map(|x| x * 2);
    assert(mapped.is_ok() == r.is_ok());
}

pub fn test_map_err() {
    let ok: Result<i32, &str> = Ok(5);
    let err: Result<i32, &str> = Err("oops");
    assert(ok.map_err(|e| e.len()).is_ok());
    assert(err.map_err(|e| e.len()).is_err());
}

pub fn test_map_err_preserves_ok(r: Result<i32, &str>) {
    assert(r.map_err(|e| e.len()).is_ok() == r.is_ok());
}

// --- expect / unwrap / unwrap_err ---

pub fn test_expect() {
    let ok: Result<i32, &str> = Ok(42);
    let _ = ok.expect("should be ok");
}

pub fn test_unwrap() {
    let ok: Result<i32, &str> = Ok(42);
    let _ = ok.unwrap();
}

pub fn test_unwrap_err() {
    let err: Result<i32, &str> = Err("oops");
    let _ = err.unwrap_err();
}

pub fn test_unwrap_after_check(r: Result<i32, &str>) {
    if r.is_ok() {
        let _ = r.unwrap();
    } else {
        let _ = r.unwrap_err();
    }
}

// --- expect_err ---

pub fn test_expect_err() {
    let err: Result<i32, &str> = Err("oops");
    let _ = err.expect_err("should be err");
}

pub fn test_expect_err_after_check(r: Result<i32, &str>) {
    if r.is_err() {
        let _ = r.expect_err("should be err");
    }
}

