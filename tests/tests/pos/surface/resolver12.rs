//! An explicit import must silently shadow a glob import that brings in a
//! same-named (but distinct) item, matching real Rust's shadowing rules
//! (<https://doc.rust-lang.org/reference/items/use-declarations.html>: "Items and named imports
//! are allowed to shadow names from glob imports in the same namespace"). This must not be
//! reported as a duplicate definition, and the explicit import must be the one actually used.
#![allow(dead_code)]

use flux_attrs::*;

// Case 0: plain Rust items, no flux attributes at all, matching the shape of the original bug
// report (`use crate::debug;` colliding with a glob-imported, unrelated `debug` re-export).
mod plain_a {
    pub fn debug() {}
}

mod plain_b {
    pub fn debug() {}
}

use plain_a::debug;
use plain_b::*;

fn test_plain() {
    debug();
}

// Case 1: explicit import vs. a glob bringing in an unrelated, same-named item, this time
// through flux-attributed functions so we can also verify *which* definition resolution picked.
mod a {
    use flux_attrs::*;

    #[spec(fn(x: i32) -> i32[x + 1])]
    pub fn shift(x: i32) -> i32 {
        x + 1
    }
}

mod b {
    use flux_attrs::*;

    #[spec(fn(x: i32) -> i32[x + 2])]
    pub fn shift(x: i32) -> i32 {
        x + 2
    }
}

use a::shift;
use b::*;

// If resolution had picked up `b::shift` (or errored as a duplicate) instead of the explicit
// `a::shift`, this postcondition (`x + 1`, not `x + 2`) would fail to verify.
#[spec(fn(x: i32) -> i32[x + 1])]
pub fn test_explicit_wins(x: i32) -> i32 {
    shift(x)
}

// Case 2: same shadowing rule, but the glob brings the name in transitively through a
// re-export, mirroring the shape that originally surfaced this bug (an explicit `use` for a
// local item colliding with a glob-imported re-export of an unrelated item from elsewhere).
mod inner {
    use flux_attrs::*;

    #[spec(fn(x: i32) -> i32[x + 3])]
    pub fn dbl(x: i32) -> i32 {
        x + 3
    }
}

mod reexport {
    pub use super::inner::dbl;
}

mod local {
    use flux_attrs::*;

    #[spec(fn(x: i32) -> i32[2 * x])]
    pub fn dbl(x: i32) -> i32 {
        2 * x
    }
}

mod use_local {
    use flux_attrs::*;

    use crate::{local::dbl, reexport::*};

    #[spec(fn(x: i32) -> i32[2 * x])]
    pub fn test_explicit_wins_reexport(x: i32) -> i32 {
        dbl(x)
    }
}
