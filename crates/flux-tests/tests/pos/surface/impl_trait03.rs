//! Test that we can use `impl Trait` on a local trait

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
