//! Import a flux def from flux-core
#![allow(dead_code)]

extern crate flux_core;

use flux_attrs::*;

defs! {
    use flux_core::num::clamp;
}

#[spec(fn(x: i32) -> i32[clamp(x, 0, 10)])]
fn clamp_to_range(x: i32) -> i32 {
    if x < 0 {
        0
    } else if x > 10 {
        10
    } else {
        x
    }
}

// A qualified path to the same def resolves to what the import brought in.
#[spec(fn(x: i32{0 <= x && x < 10}) -> i32[flux_core::num::clamp(x, 0, 10)])]
fn already_in_range(x: i32) -> i32 {
    x
}

// The def is importable again from a nested module.
mod inner {
    use flux_attrs::*;

    defs! {
        use flux_core::num::clamp;
    }

    #[spec(fn(x: i32{x > 10}) -> i32[clamp(x, 0, 10)])]
    fn above_range(_x: i32) -> i32 {
        10
    }
}
