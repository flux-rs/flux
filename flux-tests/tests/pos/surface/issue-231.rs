#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(b:bool[true]))]
fn assert(_: bool) {}

// We should not check the body of the function
fn foo() {
    assert(0 < 1);
}
