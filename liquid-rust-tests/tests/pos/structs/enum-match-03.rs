#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/nat.rs"]
pub mod nat;

enum E<T> {
    A(T),
    B(i32),
    C(i32),
}

#[lr::sig(fn(E<Nat>) -> Nat)]
fn foo(x: E<i32>) -> i32 {
    match x {
        E::A(n) => n,
        _ => 0,
    }
}
