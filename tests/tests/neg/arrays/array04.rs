// Negative tests for `[T; N]` repeat array syntax (issue #1566)
use flux_attrs::*;

#[spec(fn() -> i32{v: v > 0})]
pub fn test_repeat_array_index_read() -> i32 {
    let arr = [0i32; 8];
    arr[0] //~ ERROR refinement type
}

#[spec(fn() -> usize{v: v == 0})]
pub fn test_repeat_write_then_read() -> usize {
    let mut arr = [42usize; 16];
    arr[5] = 100;
    arr[0] //~ ERROR refinement type
}

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
