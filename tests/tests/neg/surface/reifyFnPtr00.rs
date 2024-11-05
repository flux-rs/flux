#![allow(dead_code)]

fn foo(f: fn(i32) -> i32) -> i32 {
    f(10)
}

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

#[flux::sig(fn (i32{v: v > 100}) -> i32)]
fn inc(x: i32) -> i32 {
    assert(x > 100);
    x + 1
}

fn baz() -> i32 {
    foo(inc) //~ ERROR refinement type
}
