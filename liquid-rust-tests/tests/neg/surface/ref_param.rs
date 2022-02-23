#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(b:bool{b == true}) -> i32{v:v == 0})]
pub fn assert(_b: bool) -> i32 {
    0
}

#[lr::sig(fn(x: &i32{v: v >= 0}) -> i32{v:v == 0})]
pub fn ref_param(x: &i32) -> i32 {
    assert(*x > 0); //~ ERROR precondition might not hold
    0
}
