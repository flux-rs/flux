use flux_attrs::*;

defs! {
    fn foo() -> bool;

    fn foo() -> int; //~ ERROR name `foo` is defined multiple times

    opaque sort Bag;

    opaque sort Bag; //~ ERROR name `Bag` is defined multiple times

    // Qualifiers and axioms share a namespace that is separate from funcs, so this doesn't clash
    // with `foo` above.
    qualifier foo(x: int) {
        x > 0
    }

    qualifier foo(x: int) { //~ ERROR name `foo` is defined multiple times
        x > 0
    }

    axiom foo(x: int) { x == x } //~ ERROR name `foo` is defined multiple times
}

// Qualifiers and axioms are scoped to the module declaring them (like funcs and sorts), so `bar`
// doesn't clash across module boundaries.
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
        qualifier bar(x: int) {
            x > 0
        }
    }
}
