#![allow(dead_code)]

use flux_rs::attrs::*;

trait MyTrait {
    fn baz(&self) -> usize;
}

struct Add1;

impl MyTrait for Add1 {
    fn baz(&self) -> usize {
        1
    }
}

#[spec(fn(x: i32{v: v == <Add1 as MyTrait>::f(0) }))]
fn test00(_x: i32) {}

fn test01() {
    test00(1);
}

#[flux::specs {

    trait MyTrait {
        #[reft]
        fn f(x: int) -> int;

        fn baz(&Self) -> usize[<Self as MyTrait>::f(0)];

    }

    impl MyTrait for Add1 {
        #[reft] fn f(x: int) -> int {
            x + 1
        }

        fn baz(&Self) -> usize[1];
    }

}]
const _: () = ();
