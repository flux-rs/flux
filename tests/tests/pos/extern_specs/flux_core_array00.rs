extern crate flux_core;
use flux_rs::assert;

// --- TryFrom<&[T]> for &[T; N] ---

pub fn test_ok_when_exact_length(xs: &[i32]) {
    if xs.len() == 4 {
        assert(<&[i32; 4]>::try_from(xs).is_ok());
    }
}

pub fn test_err_when_wrong_length(xs: &[i32]) {
    if xs.len() != 4 {
        assert(<&[i32; 4]>::try_from(xs).is_err());
    }
}

pub fn test_unwrap_after_length_check(xs: &[i32]) {
    if xs.len() == 4 {
        let _arr: &[i32; 4] = <&[i32; 4]>::try_from(xs).unwrap();
    }
}

pub fn test_branch_on_result(xs: &[i32]) {
    match <&[i32; 4]>::try_from(xs) {
        Ok(_arr) => assert(xs.len() == 4),
        Err(_) => assert(xs.len() != 4),
    }
}

// --- TryFrom<&mut [T]> for &mut [T; N] ---

pub fn test_mut_ok_when_exact_length(xs: &mut [i32]) {
    if xs.len() == 4 {
        assert(<&mut [i32; 4]>::try_from(xs).is_ok());
    }
}

pub fn test_mut_err_when_wrong_length(xs: &mut [i32]) {
    if xs.len() != 4 {
        assert(<&mut [i32; 4]>::try_from(xs).is_err());
    }
}

pub fn test_mut_unwrap_after_length_check(xs: &mut [i32]) {
    if xs.len() == 4 {
        let _arr: &mut [i32; 4] = <&mut [i32; 4]>::try_from(xs).unwrap();
    }
}
