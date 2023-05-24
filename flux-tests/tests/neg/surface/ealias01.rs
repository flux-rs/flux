#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    fn leq(x: int, y: int) -> bool { x <= y }
    fn nat(x: int) -> bool { leq(0,x) }
}]

#[flux::alias(type Nat() = i32{v:nat(v)})]
type Nat = i32;

#[flux::sig(fn(x:Nat) -> Nat)]
pub fn test2(x: Nat) -> Nat {
    x - 1 //~ ERROR refinement type
}
