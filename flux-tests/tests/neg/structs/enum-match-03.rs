#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/nat.rs"]
pub mod nat;

pub enum E<T> {
    A(T),
    B(i32),
    C(i32),
}

#[lr::sig(fn(E<i32>) -> Nat)]
pub fn foo(x: E<i32>) -> i32 { //~ ERROR postcondition might not hold
    match x {
        E::A(n) => n,
        _ => 0,
    }
}
