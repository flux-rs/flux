// Without `#[assume_parametric]` on the impl, the refinement on `T` is lost
use flux_attrs::*;

struct S<T> {
    f: T,
}
trait MyTrait {}

impl MyTrait for i32 {}

impl<T: MyTrait> S<T> {
    fn get(&self) -> &T {
        &self.f
    }
}

#[spec(fn(&S<i32{v: v > 0}>) -> i32{v: v > 0})]
fn test(x: &S<i32>) -> i32 {
    *x.get() //~ERROR refinement type error
}
