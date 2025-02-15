// Testing that we properly map generics in trait's default associated refinement
// body into the impl.

use flux_rs::attrs::*;

trait MyTrait {
    #![reft(fn p(x: Self) -> bool { true })]

    #[sig(fn(&Self{v: <Self as MyTrait>::p(v)}))]
    fn method(&self);
}

impl MyTrait for i32 {
    #[sig(fn(&Self{v: <Self as MyTrait>::p(v)}))]
    fn method(&self) {}
}

impl<T> MyTrait for S<T> {
    #[sig(fn(&Self{v: <Self as MyTrait>::p(v)}))]
    fn method(&self) {}
}

struct S<T> {
    f: T,
}
