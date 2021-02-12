#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn(x: {b: usize | b >= 0usize}) -> {b: usize | b == x}")]
pub fn identity(x: usize) -> usize {
    let mut i = 0;
    while i < x {
        i += 1;
    }
    i
}
