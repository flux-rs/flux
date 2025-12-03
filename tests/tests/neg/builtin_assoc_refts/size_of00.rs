use flux_rs::attrs::*;

struct S {
    x: i32,
    y: i32,
}

#[spec(fn() requires T::size_of() == 4)]
fn requires_size_4<T>() {}

fn test01() {
    requires_size_4::<i64>(); //~ ERROR refinement type
}

fn test02() {
    requires_size_4::<S>(); //~ ERROR refinement type
}
