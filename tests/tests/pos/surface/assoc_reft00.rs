use flux_rs::attrs::*;

// Step 1 : declare -------------------------------
pub trait MyTrait {
    #![reft(fn f(self: Self) -> bool)]

    fn method(&self) -> i32;
}

#[trusted]
#[sig(fn(&{T[@x] | <T as MyTrait>::f(x)}))] // TODO: check against trait-spec
pub fn bob<T: MyTrait>(x: &T) {
    x.method();
}

pub struct S1;
impl S1 {
    #[trusted]
    #[sig(fn(&{T[@x] | <T as MyTrait>::f(x)}))]
    pub fn bob<T: MyTrait>(x: &T) {
        x.method();
    }
}

pub struct S2<T> {
    pub f: T,
}

impl<T: MyTrait> S2<T> {
    #[trusted]
    #[sig(fn(&{T[@x] | <T as MyTrait>::f(x)}))]
    pub fn bob(x: &T) {
        x.method();
    }
}
