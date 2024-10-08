// structurally equal but different types
#[flux::sig(fn(x: i32) -> i32)] //~ ERROR incompatible refinement annotation
pub fn test01(x: bool) -> i32 {
    0
}

// mismatch in generic argument
#[flux::sig(fn(x: Option<i64>) -> i64)] //~ ERROR incompatible refinement annotation
pub fn test02(x: Option<i32>) -> i64 {
    0
}

// mismatch return type
#[flux::sig(fn(x: i32) -> i32)] //~ ERROR incompatible refinement annotation
pub fn test03(x: i32) -> bool {
    x > 0
}

// wrong number of function arguments
#[flux::sig(fn(x:i32, y:i32) -> i32)] //~ ERROR incompatible refinement annotation
pub fn test04(x: i32) -> i32 {
    x + 1
}

// mutability mismatch
#[flux::sig(fn(x: &mut i32))] //~ ERROR incompatible refinement annotation
pub fn test05(x: &i32) {}

// expected a return type
#[flux::sig(fn(x:i32) -> i32)] //~ ERROR incompatible refinement annotation
pub fn test06(x: i32) {}

// missing return type
#[flux::sig(fn())] //~ ERROR incompatible refinement annotation
fn test07() -> i32 {
    0
}

// structurally different types
#[flux::sig(fn(x: f32))] //~ ERROR incompatible refinement annotation
fn test08(f: &mut f32) {}

// structurally different types
#[flux::sig(fn(x: &mut f32))] //~ ERROR incompatible refinement annotation
fn test09(f: f32) {}

// strong reference for a non &mut T
#[flux::sig(fn(x: &strg i32) ensures x: i32)] //~ ERROR incompatible refinement annotation
fn test10(x: &i32) {}

// constrained type for a non path
#[flux::sig(fn(x: i32{x > 0}))] //~ ERROR incompatible refinement annotation
fn test11(x: &mut i32) {}

// tuples differ in length
#[flux::sig(fn(x: (i32, i32, i32)))] //~ ERROR incompatible refinement annotation
fn test12(x: (i32, i32)) {}

// base type differ
#[flux::sig(fn(x: &[i32]))] //~ ERROR incompatible refinement annotation
fn test13(x: &i32) {}

// TODO(nilehmann) uncomment when we support raw pointer in the surface syntax
// #[flux::sig(fn(x: *mut i64))]
// fn test14(x: *mut i32) {}
