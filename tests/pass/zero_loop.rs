#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: {b: usize | b >= 0usize}) -> {r: usize | r == 0usize}")]
fn zero(mut x: i32) -> i32 {
    while x > 0 {
        x -= 1;
    }
    x
}
