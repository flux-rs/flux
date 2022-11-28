#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(b:bool[true]))]
pub fn assert(_: bool) {}

pub fn foo() {
    assert(0 < 1);
}
