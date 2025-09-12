use flux_rs::attrs::*;

const N: i32 = 0;

defs! {
    fn foo() -> int {
        N(0) //~ ERROR constant not allowed in this position
    }
}
