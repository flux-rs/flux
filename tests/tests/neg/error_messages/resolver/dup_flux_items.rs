use flux_attrs::*;

defs! {
    fn foo() -> bool;

    fn foo() -> int; //~ ERROR name `foo` is defined multiple times

    // Qualifiers are checked in a separate, crate-global namespace, so this doesn't clash
    // with `foo` above.
    qualifier foo(x: int) {
        x > 0
    }

    qualifier foo(x: int) { //~ ERROR name `foo` is defined multiple times
        x > 0
    }
}
