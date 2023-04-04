#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int, b: int)]
#[flux::invariant(a > 0)]
#[flux::invariant(b > 0)]
pub struct S {
    #[flux::field({i32[@a] | a > 0})]
    fst: i32,
    #[flux::field({i32[@b] | b >= a})]
    snd: i32,
}
