// Test we correctly resolve type-relative associated refinements

use flux_rs::attrs::*;

#[assoc(fn pre(x: int) -> bool)]
trait MyTrait {
    #[spec(fn(x: i32{ Self::pre(x) }))]
    fn f(x: i32);
}

#[assoc(fn pre(x: int) -> bool { x > 0 })]
impl MyTrait for i32 {
    #[spec(fn(x: i32{ Self::pre(x) }))]
    fn f(x: i32) {}
}

#[spec(fn(x: i32{ T::pre(x) }))]
fn test00<T: MyTrait>(x: i32) {
    T::f(x);
}

fn test01() {
    test00::<i32>(0); //~ ERROR refinement type error
    <i32>::f(0); //~ ERROR refinement type error
}
