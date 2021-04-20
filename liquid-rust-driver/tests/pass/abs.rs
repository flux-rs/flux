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
