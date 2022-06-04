#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(&mut i32[@n]) -> i32[n])]
fn foo(x: &mut i32) -> i32 {
    *x
}

// This program should be accepted once we implement opening of mutable references
#[lr::sig(fn(&mut i32{v: v > 0}) -> i32{v : v > 0})]
fn baz(x: &mut i32) -> i32 {
    foo(x) //~ ERROR precondition might not hold
}
