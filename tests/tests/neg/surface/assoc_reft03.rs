use flux_rs::attrs::*;

pub trait MyTrait {
    #![reft(fn f(x: int) -> int { x + 1 })]
    //
}

// -----------------------------------------------------------------------------

pub struct Add1;

// Use the "default" assoc reft for Add1
impl MyTrait for Add1 {}

#[flux::sig(fn() -> i32{v: v == <Add1 as MyTrait>::f(0)})]
pub fn test1_ok() -> i32 {
    1
}

#[flux::sig(fn() -> i32{v: v == <Add1 as MyTrait>::f(0)})]
pub fn test1_fail() -> i32 {
    99 //~ ERROR: refinement type error
}

// -----------------------------------------------------------------------------

pub struct Add2;

// Specify a custom assoc reft for Add2
impl MyTrait for Add2 {
    #![reft(fn f(x: int) -> int { x + 2 })]
    //
}

#[flux::sig(fn() -> i32{v: v == <Add2 as MyTrait>::f(0)})]
pub fn test2() -> i32 {
    2
}
