#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: usize) -> {b: usize | b == x + 1usize}")]
pub fn successor(x: usize) -> usize {
    x + 1
}

#[liquid::ty("fn(x: usize) -> {b: usize | b > x}")]
pub fn greater_than_arg(x: usize) -> usize {
    x + 1
}
