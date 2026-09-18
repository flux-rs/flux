use flux_attrs::*;

defs! {
    fn foo() -> bool;

    fn foo() -> int; //~ ERROR name `foo` is defined multiple times

    opaque sort Bag;

    opaque sort Bag; //~ ERROR name `Bag` is defined multiple times

    // Qualifiers are checked in a separate, crate-global namespace, so this doesn't clash
    // with `foo` above.
    qualifier foo(x: int) {
        x > 0
    }

    qualifier foo(x: int) { //~ ERROR name `foo` is defined multiple times
        x > 0
    }
}

// Qualifiers (and primop-props) are global: `bar` clashes across module boundaries too, unlike
// funcs/sorts which are scoped per-module.
mod mod_a {
    use flux_attrs::*;

    defs! {
        qualifier bar(x: int) {
            x > 0
        }
    }
}

mod mod_b {
    use flux_attrs::*;

    defs! {
        qualifier bar(x: int) { //~ ERROR name `bar` is defined multiple times
            x > 0
        }
    }
}
