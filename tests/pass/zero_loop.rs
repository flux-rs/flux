#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: {b: i32 | b >= 0i32}) -> {r: i32 | r == 0i32}")]
fn zero(mut x: i32) -> i32 {
    while x > 0 {
        x -= 1;
    }
    x
}
