#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn(bool@true) -> i32@0)]
pub fn assert(_b: bool) -> i32 {
    0
}

#[lr::ty(fn(&i32{v: v >= 0}) -> i32@0)]
pub fn ref_param(x: &i32) -> i32 {
    assert(*x + 1 > 0);
    0
}
