#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[lr::sig(fn(x:Nat) -> Nat)]
pub fn test0(x: i32) -> i32 {
    x - 1 //~ ERROR postcondition
}

#[lr::sig(fn(x:Lb[0]) -> Lb[10])]
pub fn test2(x: i32) -> i32 {
    x + 1 //~ ERROR postcondition
}
