#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int, b: int)]
struct Pair {
    #[flux::field(i32[a])]
    fst: i32,
    #[flux::field(i32[b])]
    snd: i32,
}
