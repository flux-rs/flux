#![flux::defs {
    fn nat(x: int) -> bool { 0 <= x }
}]

#[flux::sig(fn(x: i32{ nat(x) }) -> i32{v: nat(v)})]
pub fn test1(x: i32) -> i32 {
    x + 1
}

#[flux::alias(type Nat = i32{v: nat(v)})]
type Nat = i32;

#[flux::sig(fn(x: Nat) -> i32{v: v >= 0})]
pub fn test2(x: Nat) -> i32 {
    x + 1
}
