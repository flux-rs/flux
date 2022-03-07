#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(b:bool[true]) -> i32[0])]
pub fn assert(_b: bool) -> i32 {
    0
}

#[lr::sig(fn(x: &i32{v:0<=v}) -> i32[0])]
pub fn ref_param(x: &i32) -> i32 {
    assert(*x + 1 > 0);
    0
}
