#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: {x: usize |  x >= 0usize}) -> {s: usize | s == 0usize}")]
pub fn zero_cond(x: usize) -> usize {
    match x {
        0 => x,
        _ => 0,
    }
}
