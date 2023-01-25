#![feature(register_tool)]
#![register_tool(flux)]

struct S1<T1, T2> {
    x: T1,
    y: T2,
}

type S2<T> = S1<T, T>;

// mismatched type inside type alias generic argument
#[flux::sig(fn(x: S2<i64>) -> i64)] //~ ERROR invalid refinement
fn test00(x: S2<i32>) -> i64 {
    0
}

// wrong number of generic arguments for alias
#[flux::sig(fn(x: S2<i64, i32>) -> i64)] //~ ERROR this type alias must take 1 generic argument but 2 generic arguments were supplied
fn test01(x: S2<i32>) -> i64 {
    0
}
