use flux_rs::attrs::*;

struct S {
    x: i32,
    y: i32,
}

#[spec(fn() requires T::size_of() == 8)]
fn requires_size_8<T>() {}

fn test01() {
    requires_size_8::<i64>()
}

fn test02() {
    requires_size_8::<S>()
}
