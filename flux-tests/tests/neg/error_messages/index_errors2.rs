#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(x:int, y:int)]
pub struct Pair {
    #[flux::field(i32[@x])]
    pub x: i32,
    #[flux::field(i32[@y])]
    pub y: i32,
}

// Factored into separate file (from index_errors.rs) as
// rustc seems to mysteriously drop this, perhaps due to
// many other previous/other errors.

#[flux::sig(fn(Pair[@p]) -> i32[p])] //~ ERROR mismatched sorts
pub fn mytuple2(p: Pair) -> i32 {
    p.x
}
