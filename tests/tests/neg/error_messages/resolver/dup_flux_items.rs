use flux_rs::attrs::*;

defs! {
    fn foo() -> bool;

    fn foo() -> int; //~ ERROR name `foo` is defined multiple times

    qualifier foo(x: int) {  //~ ERROR name `foo` is defined multiple times
        x > 0
    }
}
