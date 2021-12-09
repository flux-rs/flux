#![feature(register_tool)]
#![register_tool(lr)]

#[lr::ty(fn<n: int, m: int{m > n}>(bool, i32@n, i32@m) -> i32{v: v >= 0})]
pub fn ref_join(b: bool, n: i32, m: i32) -> i32 {
    let mut x = n;
    let mut y = m;
    let r;
    if b {
        r = &mut x;
    } else {
        r = &mut y;
    }
    *r += 1;
    *r - n
}
