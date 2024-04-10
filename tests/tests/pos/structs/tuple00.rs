

#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

#[flux::sig(fn((Nat, Nat)) -> Nat)]
pub fn test1(pair: (Nat, Nat)) -> Nat {
    pair.0
}

#[flux::sig(fn() -> (Nat, i32))]
pub fn test2() -> (Nat, i32) {
    (10, 0)
}
