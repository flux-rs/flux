#![feature(register_tool)]
#![register_tool(lr)]

// Tests that the desugaring/resolving does not fail when a refinement
// uses a variable (`y`) that is bound "later" than the occurrence.

#[lr::sig(fn(x: i32{y < x}, y: i32) -> i32)]
pub fn foo(x: i32, y: i32) -> i32 {
    y - x
}
