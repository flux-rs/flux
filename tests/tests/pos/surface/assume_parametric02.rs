// `#[assume_parametric]` on a trait impl applies to its methods
use flux_attrs::*;

struct S<T> {
    f: T,
}
trait MyTrait {}

impl MyTrait for i32 {}

trait Getter {
    type Out;
    fn get(&self) -> &Self::Out;
}

#[assume_parametric(T)]
impl<T: MyTrait> Getter for S<T> {
    type Out = T;
    fn get(&self) -> &T {
        &self.f
    }
}

#[spec(fn(&S<i32{v: v > 0}>) -> i32{v: v > 0})]
fn test(x: &S<i32>) -> i32 {
    *x.get()
}
