#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn(bool) -> i32{v : v >= 0})]
pub fn test(b: bool) -> i32 {
    let mut x = 0;
    let mut y = 0;
    let mut z = 0;
    let r1;
    let r2;
    if b {
        if b {
            r1 = &mut x;
        } else {
            r1 = &mut y;
        }
        r2 = &mut *r1;
    } else {
        r2 = &mut z;
    }
    *r2 += 1;
    x
}
