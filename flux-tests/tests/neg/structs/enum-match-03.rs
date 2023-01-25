#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

pub enum E<T> {
    A(T),
    B(i32),
    C(i32),
}

#[flux::sig(fn(E<i32>) -> Nat)]
pub fn foo(x: E<i32>) -> Nat {
    match x {
        E::A(n) => n, //~ ERROR postcondition might not hold
        _ => 0,
    }
}
