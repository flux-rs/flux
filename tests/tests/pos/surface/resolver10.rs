//! Test deeper/multi-level nested imports.
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
            fn triple(x: int) -> int { 3 * x }
            fn quad(x: int) -> int { 4 * x }
        }

        pub mod mod_x {
            use flux_attrs::*;

            defs! {
                fn leaf(x: int) -> int { x + 3 }
            }
        }
    }

    pub mod mod_c {
        use flux_attrs::*;

        defs! {
            fn plus5(x: int) -> int { x + 5 }
        }
    }
}

// Nested-within-nested: a nested group containing another nested group alongside a plain item.
defs! {
    use mod_a::{mod_b::{triple, quad}, shift};
}

#[sig(fn(x: i32) -> i32[triple(x)])]
pub fn test_nested_in_nested_triple(x: i32) -> i32 {
    3 * x
}

#[sig(fn(x: i32) -> i32[quad(x)])]
pub fn test_nested_in_nested_quad(x: i32) -> i32 {
    4 * x
}

#[sig(fn(x: i32) -> i32[shift(x)])]
pub fn test_nested_in_nested_shift(x: i32) -> i32 {
    x + 1
}

mod three_levels {
    use flux_attrs::*;

    // Three levels deep.
    defs! {
        use crate::mod_a::{mod_b::{mod_x::{leaf}}};
    }

    #[sig(fn(x: i32) -> i32[leaf(x)])]
    pub fn test_three_levels(x: i32) -> i32 {
        x + 3
    }
}

mod independent_siblings {
    use flux_attrs::*;

    // Independent sibling groups: state from the `mod_b` branch must not leak into `mod_c`.
    defs! {
        use crate::mod_a::{mod_b::{triple}, mod_c::{plus5}};
    }

    #[sig(fn(x: i32) -> i32[triple(x)])]
    pub fn test_sibling_triple(x: i32) -> i32 {
        3 * x
    }

    #[sig(fn(x: i32) -> i32[plus5(x)])]
    pub fn test_sibling_plus5(x: i32) -> i32 {
        x + 5
    }
}

mod trailing_comma {
    use flux_attrs::*;

    // Trailing comma inside a nested group.
    defs! {
        use crate::mod_a::{shift, dbl,};
    }

    #[sig(fn(x: i32) -> i32[shift(x)])]
    pub fn test_trailing_comma_shift(x: i32) -> i32 {
        x + 1
    }

    #[sig(fn(x: i32) -> i32[dbl(x)])]
    pub fn test_trailing_comma_dbl(x: i32) -> i32 {
        2 * x
    }
}
