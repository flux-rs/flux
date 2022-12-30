#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(x:int, y:int)]
pub struct Pair {
    #[flux::field(i32[@x])]
    pub x: i32,
    #[flux::field(i32[@y])]
    pub y: i32,
}

#[flux::sig(fn(Pair[@p]) -> i32[p.z])] //~ ERROR no field `z` on refinement parameters for struct `Pair`
pub fn mytuple4(p: Pair) -> i32 {
    p.x
}

#[flux::sig(fn(p: i32) -> i32[p.z])] //~ ERROR `int` is a primitive sort
pub fn bob(p: i32) -> i32 {
    p
}
