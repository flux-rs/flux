// test that we correctly encode different associated refinements from the same trate as different
// constants in smt

use flux_rs::{assert, attrs::*};

trait Trait {
    #![reft(
        fn p1(n: int) -> bool;
        fn p2(b: bool) -> bool;
    )]
    //
}

#[sig(fn(x: i32{ <T as Trait>::p1(x) }, y: bool { <T as Trait>::p2(y) }))]
fn test00<T: Trait>(x: i32, y: bool) {
    assert(x > 0);
}
