#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(x:int, y:int)]
pub struct Pair {
    #[flux::field(i32[@x])]
    pub x: i32,
    #[flux::field(i32[@y])]
    pub y: i32,
}

#[flux::sig(fn(Pair[@p,@q,@r]) -> i32[p])] //~ ERROR this type takes 1 or 2 refinement arguments but 3 were found
pub fn mytuple1(p: Pair) -> i32 {
    p.x
}

#[flux::sig(fn(Pair[@p1]) -> i32[p.x])] //~ ERROR cannot find value
pub fn mytuple3(p: Pair) -> i32 {
    p.x
}

#[flux::sig(fn(i32) -> i32[@n])] //~ ERROR illegal binder
pub fn myint2(x: i32) -> i32 {
    x
}

#[flux::sig(fn(f: &mut f32) -> i32[f])] //~ ERROR invalid use of refinement parameter
fn dipa(f: &mut f32) -> i32 {
    0
}

#[flux::sig(fn(x: i32, i32[@x]))] //~ ERROR the name `x` is already used
fn stout(x: i32, y: i32) {}

#[flux::refined_by()]
pub struct Chair {
    #[flux::field(i32{v: 0 < v})]
    pub x: i32,
}

#[flux::sig(fn () -> Chair[0])] //~ ERROR this type takes 0 refinement arguments but 1 was found
pub fn mk_chair() -> Chair {
    Chair { x: 0 }
}

#[flux::sig(fn(x: T) -> i32[x])] //~ ERROR invalid use of refinement parameter
fn generic<T>(x: T) -> i32 {
    0
}
