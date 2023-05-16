#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]))]
pub fn assert(_: bool) {}

#[flux::sig(fn(bool) -> i32[0])]
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
