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

#[spec(fn [hrn p: T -> bool](x: T{p(x)}) -> T{v: p(v)})]
fn checked_parametric_id<T>(x: T) -> T {
    x
}

#[spec(fn() -> i32[42])]
fn test_parametric() -> i32 {
    let x = 42;
    let y = checked_parametric_id(x);
    y
}
