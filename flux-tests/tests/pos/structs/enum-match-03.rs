#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

pub enum E<T> {
    A(T),
    B(i32),
    C(i32),
}

#[flux::sig(fn(E<Nat>) -> Nat)]
pub fn foo(x: E<i32>) -> i32 {
    match x {
        E::A(n) => n,
        _ => 0,
    }
}
