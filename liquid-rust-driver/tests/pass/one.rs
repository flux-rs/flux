#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn() -> { b: int | b == 1 }")]
pub fn one() -> usize {
    1
}
