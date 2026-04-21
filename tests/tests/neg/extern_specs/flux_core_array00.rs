extern crate flux_core;
use flux_rs::assert;

// --- TryFrom<&[T]> for &[T; N] ---

// no length check — can't assert Ok
pub fn test_ok_without_check(xs: &[i32]) {
    assert(<&[i32; 4]>::try_from(xs).is_ok()); //~ ERROR refinement type error
}

// no length check — can't unwrap safely
pub fn test_unwrap_without_check(xs: &[i32]) {
    let _arr: &[i32; 4] = <&[i32; 4]>::try_from(xs).unwrap(); //~ ERROR refinement type error
}

// wrong length check — len == 3 does not imply len == 4
pub fn test_ok_wrong_length(xs: &[i32]) {
    if xs.len() == 3 {
        assert(<&[i32; 4]>::try_from(xs).is_ok()); //~ ERROR refinement type error
    }
}

// --- TryFrom<&mut [T]> for &mut [T; N] ---

pub fn test_mut_ok_without_check(xs: &mut [i32]) {
    assert(<&mut [i32; 4]>::try_from(xs).is_ok()); //~ ERROR refinement type error
}

pub fn test_mut_unwrap_without_check(xs: &mut [i32]) {
    let _arr: &mut [i32; 4] = <&mut [i32; 4]>::try_from(xs).unwrap(); //~ ERROR refinement type error
}
