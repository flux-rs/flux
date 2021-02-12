#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn() -> {b: usize | b == 1usize}")]
pub fn one() -> usize {
    1
}

#[liquid::ty("fn(x: usize) -> {b: usize | b == x + 1}")]
pub fn successor(x: usize) -> usize {
    x + one()
}

#[liquid::ty("fn(x: usize) -> {b: usize | b >= x}")]
pub fn greater_than_arg(x: usize) -> usize {
    x + one()
}
