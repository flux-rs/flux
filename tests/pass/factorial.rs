#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::ty("fn (x: {b: usize | b >= 0usize}) -> {b: usize | b >= x}")]
pub fn factorial(x: usize) -> usize {
    match x {
        0 => 1,
        _ => x * factorial(x - 1),
    }
}
