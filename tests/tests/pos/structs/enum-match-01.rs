#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

#[flux::sig(fn(Option<Nat>) -> Nat)]
pub fn test(x: Option<Nat>) -> Nat {
    match x {
        Some(n) => n,
        None => 0,
    }
}
