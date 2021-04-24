#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(n: int) -> { v: int | v >= 0 }")]
pub fn abs(n: i32) -> i32 {
    if n < 0 {
        -n
    } else {
        n
    }
}

#[liquid::ty("fn(n: int) -> { v: int | v >= 0 }")]
pub fn abs_mut(mut n: i32) -> i32 {
    if n < 0 {
        n = -n;
    }
    n
}
