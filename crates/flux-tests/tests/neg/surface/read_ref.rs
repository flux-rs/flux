#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]) -> i32[0])]
pub fn assert(_b: bool) -> i32 {
    0
}

#[flux::sig(fn() -> i32[0])]
pub fn read_ref() -> i32 {
    let x = 0;
    let r = &x;
    assert(*r > 0); //~ ERROR refinement type error
    0
}
