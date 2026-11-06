extern crate flux_core;

pub fn test_unwrap_unchecked(r: Result<i32, &str>) {
    let _ = unsafe { r.unwrap_unchecked() }; //~ ERROR refinement type error
}

pub fn test_unwrap_err_unchecked(r: Result<i32, &str>) {
    let _ = unsafe { r.unwrap_err_unchecked() }; //~ ERROR refinement type error
}

pub fn test_unwrap_unchecked_on_err() {
    let err: Result<i32, &str> = Err("oops");
    let _ = unsafe { err.unwrap_unchecked() }; //~ ERROR refinement type error
}

pub fn test_unwrap_err_unchecked_on_ok() {
    let ok: Result<i32, &str> = Ok(1);
    let _ = unsafe { ok.unwrap_err_unchecked() }; //~ ERROR refinement type error
}
