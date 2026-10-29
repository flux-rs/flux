use flux_attrs::*;

defs! {
    fn foo(x: int) -> int;

    axiom FooBadArg(x: bool) {
        foo(x) > 0 //~ ERROR mismatched sorts
    }
}
