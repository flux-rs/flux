#![feature(register_tool)]
#![register_tool(flux)]

#[flux::alias(type Nat() = i32{v: 0 <= v})]
type _Nat = i32;

#[flux::alias(type Lb(n) = i32{v: n <= v})]
type _Lb = i32;

#[flux::sig(fn(x:Nat) -> Nat)]
pub fn test0(x: i32) -> i32 {
    x - 1 //~ ERROR postcondition
}

#[flux::sig(fn(x:Lb[0]) -> Lb[10])]
pub fn test2(x: i32) -> i32 {
    x + 1 //~ ERROR postcondition
}
