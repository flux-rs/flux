#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int, b: int)]
pub struct S {
    #[flux::field(i32[@a])]
    a: i32,
    #[flux::field(i32[@b])]
    b: i32,
}

#[flux::sig(fn(S[true, 1]))] //~ ERROR mismatched sorts
pub fn foo(_: S) {}
