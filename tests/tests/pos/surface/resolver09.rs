//! Test that nested imports (`use a::{b, c}`) resolve correctly.
#![allow(dead_code)]

use flux_attrs::*;

mod mod_a {
    use flux_attrs::*;

    defs! {
        fn shift(x: int) -> int { x + 1 }
        fn dbl(x: int) -> int { 2 * x }
    }

    pub mod mod_b {
        use flux_attrs::*;

        defs! {
            fn c(x: int) -> int { x + 1 }
            fn d(x: int) -> int { x + 2 }
        }
    }

    pub mod nested {
        use flux_attrs::*;

        defs! {
            fn dbl(x: int) -> int { 3 * x }
        }
    }
}

// Basic nested import: two items from the same module.
defs! {
    use mod_a::{shift, dbl};
}

#[sig(fn(x: i32) -> i32[shift(x)])]
pub fn test_basic_nested(x: i32) -> i32 {
    x + 1
}

#[sig(fn(x: i32) -> i32[dbl(x)])]
pub fn test_basic_nested2(x: i32) -> i32 {
    2 * x
}

mod use_multi_segment {
    use flux_attrs::*;

    // Multi-segment prefix before the braces: both `mod_a` and `mod_b` must resolve as modules.
    defs! {
        use crate::mod_a::mod_b::{c, d};
    }

    #[sig(fn(x: i32) -> i32[c(x)])]
    pub fn test_multi_segment_prefix(x: i32) -> i32 {
        x + 1
    }

    #[sig(fn(x: i32) -> i32[d(x)])]
    pub fn test_multi_segment_prefix2(x: i32) -> i32 {
        x + 2
    }
}

mod use_mixed {
    use flux_attrs::*;

    // Mix a plain item with a further-nested path inside the same braces.
    defs! {
        use crate::mod_a::{shift, nested::dbl};
    }

    #[sig(fn(x: i32) -> i32[shift(x)])]
    pub fn test_mixed(x: i32) -> i32 {
        x + 1
    }

    #[sig(fn(x: i32) -> i32[dbl(x)])]
    pub fn test_mixed2(x: i32) -> i32 {
        3 * x
    }
}
