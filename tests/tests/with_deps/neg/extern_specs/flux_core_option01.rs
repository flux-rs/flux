extern crate flux_core;

pub fn test_unwrap_unchecked(x: Option<i32>) {
    let _ = unsafe { x.unwrap_unchecked() }; //~ ERROR refinement type error
}

pub fn test_unwrap_unchecked_none() {
    let x: Option<i32> = None;
    let _ = unsafe { x.unwrap_unchecked() }; //~ ERROR refinement type error
}
