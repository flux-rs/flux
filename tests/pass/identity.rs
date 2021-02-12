#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: usize) -> {b: usize | b == x}")]
pub fn identity(x: usize) -> usize {
    x
}
