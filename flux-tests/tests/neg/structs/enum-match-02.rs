#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[lr::sig(fn () -> Option<Nat>)]
pub fn test1() -> Option<i32> { //~ ERROR postcondition might not hold
    let t = 5 - 7;
    Option::Some(t)
}
