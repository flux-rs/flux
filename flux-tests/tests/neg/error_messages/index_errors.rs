#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by()]
pub struct Chair {
    #[flux::field(i32{v: 0 < v})]
    pub x: i32,
}

#[flux::sig(fn () -> Chair[0])] //~ ERROR this type takes 0 refinement parameters but 1 was found
pub fn mk_chair() -> Chair {
    Chair { x: 0 }
}

#[flux::sig(fn (c:Chair) -> i32)] //~ ERROR this type takes 0 refinement parameters but 1 was found
pub fn use_chair(c: Chair) -> i32 {
    c.x
}

#[flux::refined_by(x:int, y:int)]
pub struct Pair {
    #[flux::field(i32[@x])]
    pub x: i32,
    #[flux::field(i32[@y])]
    pub y: i32,
}

#[flux::sig(fn(Pair[@p,@q,@r]) -> i32[p])] //~ ERROR this type takes 1 or 2 refinement parameters but 3 were found
pub fn mytuple1(p: Pair) -> i32 {
    p.x
}

#[flux::sig(fn(Pair[@p]) -> i32[p])] //~ ERROR invalid use of refinement parameter
pub fn mytuple2(p: Pair) -> i32 {
    p.x
}
