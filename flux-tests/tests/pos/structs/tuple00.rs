#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[flux::sig(fn((Nat, i32)) -> Nat)]
pub fn test1(pair: (i32, i32)) -> i32 {
    pair.0
}

#[flux::sig(fn() -> (Nat, i32))]
pub fn test2() -> (i32, i32) {
    (10, 0)
}
