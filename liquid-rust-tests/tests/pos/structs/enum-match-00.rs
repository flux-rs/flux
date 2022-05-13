#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/nat.rs"]
pub mod nat;

#[lr::sig(fn (x:Option<Nat>) -> Nat)] 
pub fn test(x:Option<i32>) -> i32 {
    match x {
        Some(n) => n,
        None => 0,
    }
}
