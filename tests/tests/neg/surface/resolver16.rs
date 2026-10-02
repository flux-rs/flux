mod i32 {
    pub const MAX: i32 = 0;
}

// The specification refers to the module constant, not the primitive's MAX.
#[flux::spec(fn() -> i32[i32::MAX])]
fn wrong() -> i32 {
    2147483647 //~ ERROR refinement type error
}
