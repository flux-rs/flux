#![feature(register_tool)]
#![register_tool(lr)]

#[lr::refined_by(a: int, b: int)]
struct Pair {
    #[lr::field(i32 @ a)]
    fst: i32,
    #[lr::field(i32 @ b)]
    snd: i32,
}
