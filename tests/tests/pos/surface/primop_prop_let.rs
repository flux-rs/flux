// Test using let-bindings inside primop props

use flux_rs::attrs::*;

#[spec(fn() -> u8[4])]
pub const fn foo() -> u8 {
    1 << 2
}

defs! {
    property ShiftByTwo[<<](x, y) {
        let two = 2;
        let four = 4;
        [<<](x, two) == four*x
    }
}
