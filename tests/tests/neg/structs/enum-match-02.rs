#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

#[flux::sig(fn () -> Option<Nat>)]
pub fn test1() -> Option<Nat> {
    let t = 5 - 7;
    Option::Some(t) //~ ERROR refinement type error
}
