#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: int) -> { b: int | b == x }")]
pub fn identity(x: usize) -> usize {
    x
}
