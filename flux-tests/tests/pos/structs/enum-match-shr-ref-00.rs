#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[flux::sig(fn(&Option<Nat>) -> Nat)]
pub fn foo(opt: &Option<i32>) -> i32 {
    match opt {
        Some(x) => *x,
        None => 0,
    }
}
