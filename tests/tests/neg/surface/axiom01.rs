// Test that `axiom`s about primops only prove what they say

use flux_attrs::*;

defs! {
    axiom AndLe(x: int, y: int) {
        (0 <= x && 0 <= y) => [&](x, y) <= x
    }
}

#[spec(fn(x: u32, y: u32) -> u32{v: v <= y})]
pub fn test(x: u32, y: u32) -> u32 {
    x & y //~ ERROR refinement type
}
