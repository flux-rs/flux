#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[flux::sig(fn(x:Nat) -> Nat)]
pub fn test0(x: i32) -> i32 {
    x - 1 //~ ERROR postcondition
}

#[flux::sig(fn(x:Lb[0]) -> Lb[10])]
pub fn test2(x: i32) -> i32 {
    x + 1 //~ ERROR postcondition
}
