use flux_attrs::*;

defs! {
    fn foo(x: int) -> int;

    axiom FooNotBool(x: int) {
        foo(x) + 1 //~ ERROR mismatched sorts
    }
}
