#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/rvec.rs"]
mod rvec;
use rvec::RVec;

#[flux::sig(fn(b: bool, n:i32, m:i32{n < m}) -> i32{v: 0 <= v})]
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

#[flux::sig(fn(&mut RVec<i32>[@n], bool) -> i32[0] requires n >= 2)]
pub fn test1(vec: &mut RVec<i32>, b: bool) -> i32 {
    let r;
    if b {
        r = &mut vec[0];
    } else {
        r = &mut vec[1];
    }
    *r = 12;
    0
}

#[flux::sig(fn(bool) -> i32{v: v > 0})]
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

#[flux::sig(fn(bool) -> i32{v: v > 0})]
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

#[flux::sig(fn(x: &mut i32{v: 0 <= v}))]
pub fn test4(x: &mut i32) {
    *x += 1;
}
