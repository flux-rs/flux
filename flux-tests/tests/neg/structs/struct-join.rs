#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int)]
pub struct S<T> {
    #[flux::field({i32[@a] | a >= 0})]
    f1: i32,
    f2: T,
}

#[flux::sig(fn(bool, S<i32>) -> i32{v: v >= 0})]
pub fn test1(b: bool, mut s: S<i32>) -> i32 {
    if b {
        // we break the invariant
        s.f1 -= 1;
    }
    // test that the struct is not unnecessarily folded
    s.f1 //~ ERROR postcondition
}

#[flux::sig(fn(bool, S<i32>) -> i32{v: v > 0})]
pub fn test2(b: bool, s: S<i32>) -> i32 {
    let x = if b {
        drop(s);
        0
    } else {
        s.f1
    };
    // test we correctly join the uninitialized branch
    x //~ ERROR postcondition
}

#[flux::sig(fn(bool, S<Vec<i32> >) -> i32{v: v > 0})]
pub fn test3(b: bool, s: S<Vec<i32>>) -> i32 {
    let x = if b {
        drop(s.f2);
        0
    } else {
        s.f1
    };
    // test we correctly join partially moved struct
    x //~ ERROR postcondition
}
