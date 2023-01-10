#![feature(register_tool)]
#![register_tool(flux)]

type A<'a> = &'a [i32];

#[flux::sig(fn(A))]
fn dipa(x: A) {} //~ ERROR unsupported function signature
