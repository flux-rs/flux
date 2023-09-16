#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    fn nat(x: int) -> bool { leq(0, x) }
    fn leq(x: int, y: int) -> bool { x <= y }
    fn inc(x: int) -> int { x + 1 }
}]

#[flux::alias(type Nat = i32{v: nat(v)})]
type Nat = i32;

#[flux::alias(type Lb(n: int) = i32{v: leq(n, v) })]
type Lb = i32;

#[flux::sig(fn(x:Nat) -> Nat)]
pub fn test1(x: Nat) -> Nat {
    x + 1
}

#[flux::sig(fn(x: Lb(10)) -> i32{v: v >= 10})]
pub fn test2(x: Lb) -> i32 {
    x + 1
}

#[flux::sig(fn(x: i32) -> i32[inc(x)])]
pub fn test3(x: i32) -> i32 {
    x + 1
}
