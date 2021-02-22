#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn() -> {b: int | b == 1}")]
pub fn one() -> usize {
    1
}

#[liquid::ty("fn() -> {b: int | b > 0}")]
pub fn greater_than_zero() -> usize {
    1
}
