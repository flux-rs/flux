#[derive(Clone, Copy)]
#[flux::opaque]
#[flux::refined_by(p: int -> bool)]
pub struct S1;

#[flux::sig(fn(S1[|x| x > 0]) -> bool[true])]
pub fn test00(x: S1) -> bool {
    #[flux::sig(fn(x: S1) -> bool[set_is_in(x.p, set_singleton(x.p))])]
    pub fn f(_: S1) -> bool {
        true
    }
    f(x)
}

#[flux::sig(fn<T as base>(x: T, y: T{x == y}))]
fn eq<T>(x: T, y: T) {}

#[flux::sig(fn<T as base>(x: T, y: T{x > y}))]
fn gt<T>(x: T, y: T) {}

#[flux::sig(fn<T as base>(x: T, y: T{x >= y}))]
fn ge<T>(x: T, y: T) {}

#[flux::sig(fn<T as base>(x: T, y: T{x < y}))]
fn lt<T>(x: T, y: T) {}

#[flux::sig(fn<T as base>(x: T, y: T{x <= y}))]
fn le<T>(x: T, y: T) {}

#[flux::sig(fn(S1[|x| x > 0]))]
fn test_eq_lam(x: S1) {
    eq(x, x);
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
    eq(S2 { x: 0, y: 1 }, S2 { x: 0, y: 1 });
    gt(S2 { x: 1, y: 1 }, S2 { x: 0, y: 0 });
    ge(S2 { x: 1, y: 1 }, S2 { x: 1, y: 0 });
    lt(S2 { x: 0, y: 0 }, S2 { x: 1, y: 1 });
    le(S2 { x: 0, y: 0 }, S2 { x: 0, y: 1 });
}
