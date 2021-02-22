#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: usize, y: {b: usize | true}) -> {b: usize | b == x / y}")]
pub fn divide(x: usize, y: usize) -> usize {
    x / y
}
