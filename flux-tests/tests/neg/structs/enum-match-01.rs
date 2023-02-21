#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

#[flux::sig(fn(Option<i32>) -> Nat)]
pub fn test(x: Option<i32>) -> Nat {
    match x {
        Some(n) => n, //~ ERROR postcondition might not hold
        None => 0,
    }
}
