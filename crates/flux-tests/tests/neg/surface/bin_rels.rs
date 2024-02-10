#[flux::sig(fn<T as base>(x: T, y: T{x > y}))]
fn gt<T>(x: T, y: T) {}

#[flux::sig(fn<T as base>(x: T, y: T{x >= y}))]
fn ge<T>(x: T, y: T) {}

#[flux::sig(fn<T as base>(x: T, y: T{x < y}))]
fn lt<T>(x: T, y: T) {}

#[flux::sig(fn<T as base>(x: T, y: T{x <= y}))]
fn le<T>(x: T, y: T) {}

#[derive(Clone, Copy)]
#[flux::opaque]
#[flux::refined_by(p: int -> bool)]
pub struct S1;

#[flux::sig(fn(S1[|x| x > 0]))]
fn test_lambda(x: S1) {
    gt(x, x); //~ ERROR refinement type error
    ge(x, x); //~ ERROR refinement type error
    lt(x, x); //~ ERROR refinement type error
    le(x, x); //~ ERROR refinement type error
}

#[derive(Clone, Copy)]
#[flux::refined_by(x: int, y: int)]
struct S2 {
    #[flux::field(i32[x])]
    x: i32,
    #[flux::field(i32[y])]
    y: i32,
}

fn test_struct() {
    gt(S2 { x: 0, y: 0 }, S2 { x: 1, y: 1 }); //~ ERROR refinement type error
    ge(S2 { x: 1, y: 0 }, S2 { x: 1, y: 1 }); //~ ERROR refinement type error
    lt(S2 { x: 1, y: 1 }, S2 { x: 0, y: 0 }); //~ ERROR refinement type error
    le(S2 { x: 0, y: 1 }, S2 { x: 0, y: 0 }); //~ ERROR refinement type error
}
