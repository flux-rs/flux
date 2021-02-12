#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: usize, y: {b: usize | b != 0usize}) -> {b: usize | b == x / y}")]
pub fn divide(x: usize, y: usize) -> usize {
    x / y
}
