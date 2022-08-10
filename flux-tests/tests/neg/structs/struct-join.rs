#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int)]
pub struct S {
    #[flux::field({i32[@a] : a >= 0})]
    f: i32,
}

#[flux::sig(fn(bool, S) -> i32{v : v >= 0})]
pub fn test1(b: bool, mut s: S) -> i32 {
    if b {
        // we break the invariant
        s.f -= 1;
    }
    // test that the struct is not unnecessarily folded
    s.f //~ ERROR postcondition
}

#[flux::sig(fn(bool, S) -> i32{v : v > 0})]
pub fn test2(b: bool, s: S) -> i32 {
    let x = if b {
        drop(s);
        0
    } else {
        s.f
    };
    // test we correctly join the uninitialized branch
    x //~ ERROR postcondition
}
