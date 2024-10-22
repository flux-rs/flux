#![allow(unused)]

type Binop = fn(i32, i32) -> i32;

struct Foo {
    f: Binop,
}

// TODO: should actually support the below, not just leave it as `trusted`
#[flux::trusted]
fn bar(b: Binop) -> i32 {
    b(3, 4)
}

fn test00(foo: Foo) -> i32 {
    let x = bar(foo.f);
    x
}
