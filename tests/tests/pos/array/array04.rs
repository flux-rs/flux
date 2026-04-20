// Test for `[T; N]` repeat array syntax (issue #1566)
// Previously, `[0usize; 32]` was given type `[usize{v: v == 0}; 32]` which was
// too precise, causing valid index assignments to fail. The fix generates a fresh
// kvar via `with_holes()` + `replace_holes()`, checks subtyping, and the kvar
// gets inferred as unconstrained, giving the array an effectively unrestricted
// element type.

pub fn test_repeat_array_assignment() {
    let mut arr = [0usize; 32];
    arr[3] = 3;
}

pub fn test_repeat_array_index_read() {
    let arr = [0i32; 8];
    let _x = arr[0];
}

pub fn test_repeat_with_nonzero() {
    let mut arr = [42usize; 16];
    arr[5] = 100;
}
