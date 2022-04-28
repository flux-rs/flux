#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(bool[true]) -> i32[0])]
pub fn assert(_b: bool) -> i32 {
    0
}

#[lr::sig(fn(bool) -> i32[0])]
pub fn ref_join(b: bool) -> i32 {
    let x = 0;
    let y = 1;
    let mut r = &x;
    while b {
        if b {
            r = &y;
        }
    }
    assert(*r + 1 > 0);
    0
}
