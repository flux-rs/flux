// Negative tests for `[T; N]` repeat array syntax (issue #1566)

// The initial value 0 does NOT satisfy v > 0, so the return refinement is violated.
#[flux::sig(fn() -> [i32{v: v > 0}; 4])]
pub fn test_repeat_return_neg() -> [i32; 4] {
    [0; 4] //~ ERROR refinement type
}

// Out-of-bounds index on a repeat array
#[allow(unconditional_panic)]
pub fn test_repeat_oob() -> i32 {
    let arr = [0i32; 4];
    arr[10] //~ ERROR assertion might fail
}
