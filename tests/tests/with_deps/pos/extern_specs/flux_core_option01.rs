extern crate flux_core;

pub fn test_unwrap_unchecked() {
    let x: Option<i32> = Some(1);
    let _ = unsafe { x.unwrap_unchecked() };
}

pub fn test_unwrap_unchecked_after_check(x: Option<i32>) {
    if x.is_some() {
        let _ = unsafe { x.unwrap_unchecked() };
    }
}
