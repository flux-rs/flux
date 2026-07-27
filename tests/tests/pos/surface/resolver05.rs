//! Test that flux definitions can be referred to with qualified paths
#![allow(dead_code)]

use flux_attrs::*;

defs! {
    fn inc_int(x: int) -> int { x + 1 }
}

mod mod_a {
    use flux_attrs::*;

    defs! {
        fn shift(x: int) -> int { x + 1 }

        opaque sort Bag;
    }

    // defs resolve unqualified inside their own module
    #[sig(fn(x: i32) -> i32[shift(x)])]
    pub fn test_inner(x: i32) -> i32 {
        x + 1
    }
}

// def in `mod_a` used with a qualified path from the crate root
#[flux::sig(fn(x: i32) -> i32[mod_a::shift(x)])]
pub fn test_mod_path(x: i32) -> i32 {
    x + 1
}

// user sort in `mod_a` used with a qualified path
#[opaque]
#[refined_by(b: mod_a::Bag)]
pub struct WithSort {
    inner: Vec<i32>,
}

mod nested {
    use flux_attrs::*;

    defs! {
        fn dbl_int(x: int) -> int { 2 * x }
    }

    // def at the crate root used with a qualified path from a nested module
    #[flux::sig(fn(x: i32) -> i32[crate::inc_int(x)])]
    pub fn test_crate_path(x: i32) -> i32 {
        x + 1
    }

    mod inner {
        // def in the parent module used with a qualified `super` path
        #[flux::sig(fn(x: i32) -> i32[super::dbl_int(x)])]
        pub fn test_super_path(x: i32) -> i32 {
            2 * x
        }
    }
}
