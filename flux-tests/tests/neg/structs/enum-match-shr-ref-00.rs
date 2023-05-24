#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

#[flux::sig(fn(&Option<i32>) -> Nat)]
pub fn foo(opt: &Option<i32>) -> Nat {
    match opt {
        Some(x) => *x, //~ ERROR refinement type error
        None => 0,
    }
}
