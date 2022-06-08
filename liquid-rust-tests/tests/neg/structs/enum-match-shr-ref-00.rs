#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[lr::sig(fn(&Option<i32>) -> Nat)]
pub fn foo(opt: &Option<i32>) -> i32 { //~ ERROR postcondition might not hold
    match opt {
        Some(x) => *x,
        None => 0,
    }
}
