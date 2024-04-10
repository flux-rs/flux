#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

pub enum E<T> {
    A(T),
    B(i32),
    C(i32),
}

#[flux::sig(fn(E<Nat>) -> Nat)]
pub fn foo(x: E<Nat>) -> Nat {
    match x {
        E::A(n) => n,
        _ => 0,
    }
}
