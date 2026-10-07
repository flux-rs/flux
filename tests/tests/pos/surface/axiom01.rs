// Test that `axiom`s can talk about (and are triggered by) the UIFs for primops like `&`

use flux_attrs::*;

defs! {
    axiom AndLe(x: int, y: int) {
        (0 <= x && 0 <= y) => [&](x, y) <= y
    }
}

#[spec(fn(x: u32, y: u32) -> u32{v: v <= y})]
pub fn test(x: u32, y: u32) -> u32 {
    x & y
}
