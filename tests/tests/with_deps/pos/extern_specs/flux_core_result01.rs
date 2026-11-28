extern crate flux_core;

pub fn test_unwrap_unchecked() {
    let ok: Result<i32, &str> = Ok(1);
    let _ = unsafe { ok.unwrap_unchecked() };
}

pub fn test_unwrap_err_unchecked() {
    let err: Result<i32, &str> = Err("oops");
    let _ = unsafe { err.unwrap_err_unchecked() };
}

pub fn test_unwrap_unchecked_after_check(r: Result<i32, &str>) {
    if r.is_ok() {
        let _ = unsafe { r.unwrap_unchecked() };
    } else {
        let _ = unsafe { r.unwrap_err_unchecked() };
    }
}
