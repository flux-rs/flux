#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn() -> {b: usize | b == 1usize}")]
pub fn one() -> usize {
    1
}

#[liquid::ty("fn() -> {b: usize | b > 0usize}")]
pub fn greater_than_zero() -> usize {
    1
}
