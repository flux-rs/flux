//! Test that `use` participates in duplicate-definition checking like any other flux item,
//! matching rustc's E0252 (use-vs-use) and E0255 (use-vs-item).
#![allow(dead_code)]

use flux_attrs::*;

mod mod_a {
    use flux_attrs::*;

    defs! {
        fn shift(x: int) -> int { x + 1 }
        fn dbl(x: int) -> int { 2 * x }
    }
}

mod mod_b {
    use flux_attrs::*;

    defs! {
        fn shift(x: int) -> int { x + 2 }
    }
}

// `use` vs. an item already defined in the importing module.
defs! {
    fn dbl(x: int) -> int { 2 * x }

    use mod_a::dbl; //~ ERROR name `dbl` is defined multiple times
}

// `use` vs. another `use` importing the same name from a different path.
defs! {
    use mod_a::shift;

    use mod_b::shift; //~ ERROR name `shift` is defined multiple times
}
