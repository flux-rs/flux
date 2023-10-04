#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::{Lb, Nat};

#[flux::sig(fn(x: Nat) -> Nat)]
pub fn test0(x: Nat) -> Nat {
    x - 1 //~ ERROR refinement type
}

#[flux::sig(fn(x: Lb(0)) -> Lb(10))]
pub fn test2(x: Lb) -> Lb {
    x + 1 //~ ERROR refinement type
}
