// test that implementations with extra const generics work as expected

use flux_rs::attrs::*;

#[reft(fn p(x: int) -> bool)]
trait MyTrait {
    #[sig(fn() -> i32{ v: <Self as MyTrait>::p(v) })]
    fn method() -> i32;
}

struct MyStruct<const N: i32>;

// This implementation requires proving `x == N => x > N`
#[reft(fn p(x: int) -> bool { x > N })]
impl<const N: i32> MyTrait for MyStruct<N> {
    #[sig(fn() -> i32{v: v == N})]
    fn method() -> i32 {
        //~^ ERROR refinement type error
        N
    }
}
