use flux_attrs::*;

struct S<T> {
    f: T,
}
trait MyTrait {}

#[assume_parametric(T)]
fn get<T: MyTrait>(x: &S<T>) -> &T {
    &x.f
}

impl MyTrait for i32 {}

#[spec(fn(&S<i32{v: v > 0}>) -> i32{v: v > 0})]
fn test(x: &S<i32>) -> i32 {
    *get(x)
}
