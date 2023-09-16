#![feature(register_tool, custom_inner_attributes)]
#![register_tool(flux)]

struct S<T> {
    f: T,
}

#[flux::sig(fn() -> S<i32{v: v > 0}>)]
fn test00() -> S<i32> {
    S { f: 1 }
}

#[flux::sig(fn() -> S<S<i32{v: v > 0}>>)]
fn test01() -> S<S<i32>> {
    S { f: S { f: 1 } }
}

#[flux::sig(fn() -> S<S<S<i32{v: v > 0}>>>)]
fn test02() -> S<S<S<i32>>> {
    S { f: S { f: S { f: 1 } } }
}

#[flux::sig(fn() -> S<S<S<S<i32{v: v > 0}>>>>)]
fn test03() -> S<S<S<S<i32>>>> {
    S { f: S { f: S { f: S { f: 1 } } } }
}
