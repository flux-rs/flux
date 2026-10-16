// Items nested in a generic item cannot mention its generic parameters or `Self` in their specs

use flux_attrs::*;

pub fn id<T>(x: T) -> T {
    #[spec(fn(x: T))] //~ ERROR can't use generic parameters from outer item
    fn foo(x: i32) {}

    x
}

pub struct Bar;

impl Bar {
    pub fn foo() {
        #[spec(fn(x: Self))] //~ ERROR can't use generic parameters from outer item
        fn baz(x: i32) {}
    }
}
