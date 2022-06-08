#![feature(register_tool)]
#![register_tool(flux)]

#[flux::ty(fn() -> i32)]
fn rand() -> i32 {
    0
}

#[flux::ty(fn(bool) -> i32@0)]
pub fn test(b: bool) -> i32 {
    let mut x = 0;
    let mut y = 0;
    let mut r = &mut y;
    if b {
        x = rand();
        x += 1;
    } else {
        x = rand();
        r = &mut x;
    }
    0
}
