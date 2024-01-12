// Step 1 : declare -------------------------------
#[flux::generics(Self as base)]
#[flux::predicate{ f : (Self) -> bool }]
pub trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::trusted]
#[flux::sig(fn<T as base>(&{T[@x] | <T as MyTrait>::f(x)}))] // TODO: check against trait-spec
pub fn bob<T: MyTrait>(x: &T) {
    x.method();
}

pub struct S1;
impl S1 {
    #[flux::trusted]
    #[flux::sig(fn<T as base>(&{T[@x] | <T as MyTrait>::f(x)}))]
    pub fn bob<T: MyTrait>(x: &T) {
        x.method();
    }
}

pub struct S2<T> {
    pub f: T,
}
#[flux::generics(T as base)]
impl<T: MyTrait> S2<T> {
    #[flux::trusted]
    #[flux::sig(fn(&{T[@x] | <T as MyTrait>::f(x)}))]
    pub fn bob(x: &T) {
        x.method();
    }
}
