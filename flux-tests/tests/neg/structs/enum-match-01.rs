#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[flux::sig(fn (Option<i32>) -> Nat)]
pub fn test(x: Option<i32>) -> i32 { //~ ERROR postcondition might not hold
    match x {
        Some(n) => n,
        None => 0,
    }
}
