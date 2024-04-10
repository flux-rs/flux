#[path = "../../lib/nat.rs"]
pub mod nat;
use nat::Nat;

pub enum MyOpt<T> {
    Some(T),
    None,
}

#[flux::sig(fn (MyOpt<Nat>) -> Nat)]
pub fn test(x: MyOpt<Nat>) -> Nat {
    match x {
        MyOpt::Some(n) => n,
        MyOpt::None => 0,
    }
}
