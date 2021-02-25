#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty(fn (x: i32) -> {b: i32 | b >= 0i32})]
pub fn abs(mut n: i32) -> i32 {
    if n < 0 {
        n = -n;
    }
    n
}
