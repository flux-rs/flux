#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int, b: int)]
#[flux::invariant(a > b)]
pub struct S {
    #[flux::field(i32[@a])]
    fst: i32,
    #[flux::field({i32[@b] : a >= b})]
    snd: i32,
}
