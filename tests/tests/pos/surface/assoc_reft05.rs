// Test that a default associated refinement can use other associated refinement

use flux_rs::attrs::*;

trait MyTrait {
    #![reft(
        fn f(x: int) -> bool;

        fn g(x: int) -> bool {
            <Self as MyTrait>::f(x)
        }
    )]

    #[sig(fn(x: i32 { <Self as MyTrait>::f(x) }))]
    fn foo(x: i32) {}
}

struct S;

#[reft(fn f(x: int) -> bool { x > 0 })]
impl MyTrait for S {}

fn test() {
    S::foo(1);
}
