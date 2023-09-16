#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

pub enum E<T> {
    A(T),
    B(i32),
    C(i32),
}

#[flux::sig(fn(E<i32>) -> Nat)]
pub fn foo(x: E<i32>) -> Nat {
    match x {
        E::A(n) => n, //~ ERROR refinement type error
        _ => 0,
    }
}
