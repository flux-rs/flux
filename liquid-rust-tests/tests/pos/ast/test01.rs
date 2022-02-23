#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[lr::ty(fn<n: int, m: int{m > n}>(bool, i32@n, i32@m) -> i32{v: v >= 0})]
pub fn test0(b: bool, n: i32, m: i32) -> i32 {
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

#[lr::ty(fn<len: int{len >= 2}>(l: RVec<i32>@len; ref<l>, bool) -> i32@0; l: RVec<i32>@len)]
pub fn test1(vec: &mut RVec<i32>, b: bool) -> i32 {
    let r;
    if b {
        r = vec.get_mut(0);
    } else {
        r = vec.get_mut(1);
    }
    *r = 12;
    0
}

#[lr::ty(fn(bool) -> i32{v: v > 0})]
pub fn test2(b: bool) -> i32 {
    let mut x = 1;
    let mut y = 1;
    let r;
    if b {
        r = &mut x;
    } else {
        r = &mut y;
    }
    *r += 1;
    x + y
}

#[lr::ty(fn(bool) -> i32{v: v > 0})]
pub fn test3(b: bool) -> i32 {
    let mut x = 1;
    let mut y = 2;
    let mut r = &mut x;
    while b {
        if b {
            r = &mut y;
        }
        *r += 1;
    }
    x + y
}
