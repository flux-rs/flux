#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

#[flux::sig(fn((Nat, i32)) -> Nat)]
pub fn test1(pair: (Nat, i32)) -> Nat {
    pair.0 - 1 //~ ERROR postcondition
}

#[flux::sig(fn() -> (Nat, i32))]
pub fn test2() -> (Nat, i32) {
    (10 - 100, 0) //~ ERROR postcondition
}
