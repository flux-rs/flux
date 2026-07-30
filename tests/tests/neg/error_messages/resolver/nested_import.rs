//! Test error reporting for nested imports (`use a::{b, c}`).
#![allow(dead_code)]

use flux_attrs::*;

mod mod_a {
    use flux_attrs::*;

    defs! {
        fn shift(x: int) -> int { x + 1 }
        fn dbl(x: int) -> int { 2 * x }
        opaque sort Bag;
    }

    pub mod mod_b {
        use flux_attrs::*;

        defs! {
            fn triple(x: int) -> int { 3 * x }
        }
    }
}

// A failing sibling must still be reported even though an earlier sibling in the same list
// resolved successfully.
defs! {
    use mod_a::{shift, nonexistent}; //~ ERROR unresolved import
}

// `Bag` resolves (it's a sort), but it's used here as if it were a module.
defs! {
    use mod_a::{Bag::x}; //~ ERROR unresolved import
}

// Duplicate import of the same name within one nested list.
defs! {
    use mod_a::{dbl, dbl}; //~ ERROR name `dbl` is defined multiple times
}

// A failing branch nested two levels deep must still be reported even though a sibling deep
// branch (also two levels deep) resolves successfully.
defs! {
    use mod_a::{mod_b::{nonexistent}, mod_b::{triple}}; //~ ERROR unresolved import
}

// `triple` resolves (it's a func), but it's used here as if it were a module, discovered from
// inside a nested group rather than at the top level.
defs! {
    use mod_a::{mod_b::{triple::x}}; //~ ERROR unresolved import
}
