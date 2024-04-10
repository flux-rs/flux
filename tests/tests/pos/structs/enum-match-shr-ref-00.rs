#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

#[flux::sig(fn(&Option<Nat>) -> Nat)]
pub fn foo(opt: &Option<Nat>) -> Nat {
    match opt {
        Some(x) => *x,
        None => 0,
    }
}
