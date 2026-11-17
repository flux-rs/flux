// Test that a `local property` is used when checking the functions that name it in
// `#[properties(...)]`, and that properties are resolved like other flux definitions

use flux_attrs::*;

#[spec(fn(bool[true]))]
fn assert(_b: bool) {}

defs! {
    // A global property is used everywhere
    property ShiftRightByFour[>>](x, y) {
        16 * [>>](x, 4) == x
    }

    local property ShiftByTwo[<<](x, y) {
        [<<](x, 2) == 4*x
    }

    local property MaskBy[&](x, y) {
        [&](x, y) <= y
    }
}

pub fn test_global(x: u32) {
    let y = x >> 4;
    assert(16 * y == x);
}

#[properties(ShiftByTwo)]
#[spec(fn (x: u32) -> u32[16*x])]
pub fn test_local(x: u32) -> u32 {
    let x = x << 2;
    let x = x << 2;
    x
}

#[properties(ShiftByTwo, MaskBy)]
#[spec(fn (x: u32, y: u32) -> u32{v: v <= y})]
pub fn test_two(x: u32, y: u32) -> u32 {
    let _z = x << 2;
    x & y
}

pub mod props {
    use flux_attrs::*;

    defs! {
        local property OrBy[|](x, y) {
            x <= [|](x, y)
        }
    }
}

// A qualified path
#[properties(props::OrBy)]
#[spec(fn (x: u32, y: u32) -> u32{v: x <= v})]
pub fn test_path(x: u32, y: u32) -> u32 {
    x | y
}

mod imported {
    use flux_attrs::*;

    defs! {
        use crate::props::OrBy;
    }

    // An import with flux's `use`
    #[properties(OrBy)]
    #[spec(fn (x: u32, y: u32) -> u32{v: x <= v})]
    pub fn test_use(x: u32, y: u32) -> u32 {
        x | y
    }
}
