#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn() -> { b: int | b == 1 }")]
pub fn one() -> usize {
    1
}

#[liquid::ty("fn(n: int) -> { v: int | v == n }")]
pub fn id(n: usize) -> usize {
    n
}
