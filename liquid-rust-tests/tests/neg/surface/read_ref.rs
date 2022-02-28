#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(b:bool[true]) -> i32[0])]
pub fn assert(_b: bool) -> i32 {
    0
}

#[lr::sig(fn() -> i32[0])]
pub fn read_ref() -> i32 {
    let x = 0;
    let r = &x;
    assert(*r > 0); //~ ERROR precondition might not hold
    0
}
