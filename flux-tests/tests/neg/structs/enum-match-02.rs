#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[flux::sig(fn () -> Option<Nat>)]
pub fn test1() -> Option<i32> {
    let t = 5 - 7;
    Option::Some(t) //~ ERROR postcondition might not hold
}
