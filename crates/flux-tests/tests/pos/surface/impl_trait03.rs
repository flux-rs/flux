//! Test that we can use `impl Trait` on a local trait
#![feature(register_tool)]
#![register_tool(flux)]

trait Trait {
    type A;
}

struct S<T> {
    f: T,
}

impl Trait for S<i32> {
    type A = i32;
}

fn test() -> impl Trait<A = i32> {
    S { f: 0 }
}
