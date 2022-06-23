#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

pub enum MyOpt<T> {
    Some(T),
    None,
}

#[flux::sig(fn (MyOpt<Nat>) -> Nat)]
pub fn test(x: MyOpt<i32>) -> i32 {
    match x {
        MyOpt::Some(n) => n,
        MyOpt::None => 0,
    }
}
