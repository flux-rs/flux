use flux_rs::{assert, attrs::*, defs};

defs! {
    property ShiftByTwo[<<](x, y) {
       y == 2 => [<<](x, y) == 4*x
    }
}

pub fn test0() {
    let x: usize = 1 << 2;
    assert(x == 4);
}

pub fn test1() {
    let x = 1;
    let x = x << 2;
    let x = x << 2;
    assert(x == 16)
}

#[spec(fn (x: u32) -> u32[16*x])]
pub fn test2(x: u32) -> u32 {
    let x = x << 2;
    let x = x << 2;
    x
}
