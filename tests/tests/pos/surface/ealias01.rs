#![flux::defs {
    fn leq(x: int, y: int) -> bool { x <= y }
    fn nat(x: int) -> bool { leq(0,x) }
}]

#[flux::alias(type Nat = i32{v:nat(v)})]
type Nat = i32;

#[flux::sig(fn(x:Nat) -> i32{v: v >= 0})]
pub fn test2(x: Nat) -> i32 {
    x + 1
}
