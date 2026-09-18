//! Test that `flux::use` imports flux items so they can be referred to unqualified.
#![allow(dead_code)]

use flux_attrs::*;

mod mod_a {
    use flux_attrs::*;

    defs! {
        fn shift(x: int) -> int { x + 1 }

        opaque sort Bag;
    }
}

// Import a func and a sort from a sibling module.
defs! {
    use mod_a::shift;
    use mod_a::Bag;
}

#[sig(fn(x: i32) -> i32[shift(x)])]
pub fn test_use_fn(x: i32) -> i32 {
    x + 1
}

#[opaque]
#[refined_by(b: Bag)]
pub struct WithSort {
    inner: Vec<i32>,
}

mod nested {
    pub mod inner {
        use flux_attrs::*;

        defs! {
            fn dbl(x: int) -> int { 2 * x }
        }
    }
}

// Import through a multi-segment (nested module) path.
defs! {
    use nested::inner::dbl;
}

#[sig(fn(x: i32) -> i32[dbl(x)])]
pub fn test_nested_use(x: i32) -> i32 {
    2 * x
}

mod sibling {
    use flux_attrs::*;

    // Import using a `crate::` prefixed path.
    defs! {
        use crate::nested::inner::dbl;
    }

    #[sig(fn(x: i32) -> i32[dbl(x)])]
    pub fn test_crate_path_use(x: i32) -> i32 {
        2 * x
    }
}
