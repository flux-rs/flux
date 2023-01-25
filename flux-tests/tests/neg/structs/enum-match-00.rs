#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/nat.rs"]
pub mod nat;

pub enum MyOpt<T> {
    Some(T),
    None,
}

#[flux::sig(fn (MyOpt<i32>) -> Nat)]
pub fn test(x: MyOpt<i32>) -> Nat {
    match x {
        MyOpt::Some(n) => n, //~ ERROR postcondition might not hold
        MyOpt::None => 0,
    }
}
