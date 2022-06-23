#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(&mut i32[@n]) -> i32[n + 1])]
fn foo(x: &mut i32) -> i32 {
    *x + 1
}

#[flux::sig(fn(&mut i32{v: v > 0}) -> i32{v : v > 0})]
fn baz(x: &mut i32) -> i32 {
    foo(x)
}
