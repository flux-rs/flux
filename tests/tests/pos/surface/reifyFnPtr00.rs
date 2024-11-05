#![allow(dead_code)]

fn foo(f: fn(i32) -> i32) -> i32 {
    f(10)
}

#[flux::sig(fn (i32) -> i32{v:v <= 100})]
fn inc(x: i32) -> i32 {
    if x <= 100 {
        x
    } else {
        100
    }
}

fn baz() -> i32 {
    foo(inc)
}
