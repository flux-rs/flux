extern crate flux_core;
use flux_rs::assert;

// --- is_ok / is_err ---

pub fn test_is_ok(r: Result<i32, &str>) {
    assert(r.is_ok()); //~ ERROR refinement type error
}

pub fn test_is_err(r: Result<i32, &str>) {
    assert(r.is_err()); //~ ERROR refinement type error
}

// --- ok / err ---

pub fn test_ok(r: Result<i32, &str>) {
    assert(r.ok().is_some()); //~ ERROR refinement type error
}

pub fn test_err(r: Result<i32, &str>) {
    assert(r.err().is_some()); //~ ERROR refinement type error
}

// --- as_ref ---

pub fn test_as_ref_is_ok(r: Result<i32, &str>) {
    assert(r.as_ref().is_ok()); //~ ERROR refinement type error
}

// --- map / map_err ---

pub fn test_map_is_ok(r: Result<i32, &str>) {
    assert(r.map(|x| x + 1).is_ok()); //~ ERROR refinement type error
}

pub fn test_map_err_is_err(r: Result<i32, &str>) {
    assert(r.map_err(|e| e.len()).is_err()); //~ ERROR refinement type error
}

// --- expect / unwrap / unwrap_err ---

pub fn test_expect(r: Result<i32, &str>) {
    let _ = r.expect("should be ok"); //~ ERROR refinement type error
}

pub fn test_unwrap(r: Result<i32, &str>) {
    let _ = r.unwrap(); //~ ERROR refinement type error
}

pub fn test_unwrap_err(r: Result<i32, &str>) {
    let _ = r.unwrap_err(); //~ ERROR refinement type error
}

// --- expect_err ---

pub fn test_expect_err(r: Result<i32, &str>) {
    let _ = r.expect_err("should be err"); //~ ERROR refinement type error
}

