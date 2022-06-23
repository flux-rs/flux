#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]) -> i32[0])]
pub fn assert(_b: bool) -> i32 {
    0
}

#[flux::sig(fn(&i32{v : 0 <= v}) -> i32[0])]
pub fn ref_param(x: &i32) -> i32 {
    assert(*x + 1 > 0);
    0
}
