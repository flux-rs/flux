use flux_attrs::*;

defs! {
    fn foo(x: int) -> int;

    // `y` does not occur in the only pattern `foo(x)`, so the axiom cannot be instantiated
    axiom FooUncovered(x: int, y: int) { //~ ERROR ill-formed axiom
        foo(x) > y
    }
}
