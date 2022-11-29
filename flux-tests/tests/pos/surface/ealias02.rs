#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::expr(nat(x: int) -> bool { 0 <= x })]
#![flux::expr(leq(x: int, y: int) -> bool { x <= y })]
#![flux::expr(inc(x: int) -> int { x + 1 })]
#![flux::expr(leq1(x: int, y: int) -> bool { leq(x, inc(y)) })]

// https://github.com/chrisdone/sandbox/blob/master/liquid-haskell-dates.hs

#[flux::alias(type Nat() = i32{v: 0 <= v})]
type _Nat = i32;

#[flux::alias(type Lb(n) = i32{v: n <= v})]
type _Lb = i32;

#[flux::sig(fn(x:Nat) -> Nat)]
pub fn test1(x: i32) -> i32 {
    x + 1
}

#[flux::sig(fn(x:Lb[10]) -> Lb[10])]
pub fn test2(x: i32) -> i32 {
    x + 1
}
