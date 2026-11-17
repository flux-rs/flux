// Test that a `local property` is only used when checking the functions that name it

use flux_attrs::*;

#[spec(fn(bool[true]))]
fn assert(_b: bool) {}

defs! {
    local property ShiftByTwo[<<](x, y) {
        [<<](x, 2) == 4*x
    }

    local property MaskBy[&](x, y) {
        [&](x, y) <= y
    }
}

#[spec(fn (x: u32) -> u32[4*x])]
pub fn test_none(x: u32) -> u32 {
    x << 2 //~ ERROR refinement type
}

#[properties(MaskBy)]
#[spec(fn (x: u32) -> u32[4*x])]
pub fn test_wrong(x: u32) -> u32 {
    x << 2 //~ ERROR refinement type
}

#[properties(ShiftByTwo)]
#[spec(fn (x: u32, y: u32) -> u32{v: v <= y})]
pub fn test_missing(x: u32, y: u32) -> u32 {
    let _z = x << 2;
    x & y //~ ERROR refinement type
}
