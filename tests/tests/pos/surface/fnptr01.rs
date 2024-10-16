#![allow(dead_code)]

fn foo(f: fn(i32) -> i32) -> i32 {
    f(10)
}

fn bar() -> i32 {
    foo(|z| z + 1)
}
