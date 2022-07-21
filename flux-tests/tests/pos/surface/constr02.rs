#![feature(register_tool)]
#![register_tool(flux)]

// Test for
// Option<{i32[a] : a > 0}> <: Option<i32{v : v > 0 }>

#[flux::sig(fn(Option<i32{v: 0 < v}>) -> ())]
fn foo(_x: Option<i32>) {}

#[flux::sig(fn(a:i32, Option<{i32[a] : 0 < a}>) -> ())]
pub fn bar(_a: i32, y: Option<i32>) {
    foo(y)
}
