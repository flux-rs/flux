#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[flux::sig(fn(&Option<i32>) -> Nat)]
pub fn foo(opt: &Option<i32>) -> i32 {
    match opt {
        Some(x) => *x, //~ ERROR postcondition might not hold
        None => 0,
    }
}
