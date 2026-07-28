//! Test the `unresolved import` diagnostic for each failure mode of `resolve_flux_use_path`.
#![allow(dead_code)]

use flux_attrs::*;

mod mod_a {
    use flux_attrs::*;

    defs! {
        fn shift(x: int) -> int { x + 1 }

        opaque sort Bag;
    }

    struct Hidden;
}

// Single-segment name that doesn't resolve in local scope.
defs! {
    use nonexistent; //~ ERROR unresolved import
}

// First prefix segment doesn't resolve in local scope.
defs! {
    use nonexistent::foo; //~ ERROR unresolved import
}

// `mod_a` resolves, but the item doesn't exist inside it.
defs! {
    use mod_a::nonexistent; //~ ERROR unresolved import
}

// `Bag` resolves inside `mod_a`, but it's a sort, not a module.
defs! {
    use mod_a::Bag::x; //~ ERROR unresolved import
}

// `Hidden` exists in `mod_a` but isn't `pub`.
defs! {
    use mod_a::Hidden; //~ ERROR unresolved import
}
