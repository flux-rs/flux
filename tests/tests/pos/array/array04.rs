// Test for `[T; N]` repeat array syntax (issue #1566)

// Basic: write to element of a repeat array (the original bug report)
pub fn test_repeat_array_assignment() {
    let mut arr = [0usize; 32];
    arr[3] = 3;
}

// Read from a repeat array
pub fn test_repeat_array_index_read() {
    let arr = [0i32; 8];
    let _x = arr[0];
}

// Write a different value to a repeat array initialised with a non-zero constant
pub fn test_repeat_with_nonzero() {
    let mut arr = [42usize; 16];
    arr[5] = 100;
}

// The element type must satisfy the annotated return refinement.
// 0 >= 0, so kvar can be inferred as `v >= 0` which is consistent.
#[flux::sig(fn() -> [i32{v: v >= 0}; 4])]
pub fn test_repeat_return_geq_zero() -> [i32; 4] {
    [0; 4]
}

// 1 > 0, so kvar can be inferred as `v > 0`
#[flux::sig(fn() -> [i32{v: v > 0}; 4])]
pub fn test_repeat_return_pos() -> [i32; 4] {
    [1; 4]
}
