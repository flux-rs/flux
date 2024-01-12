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

#[flux::predicate{ g : (int, int) -> int }]
pub trait OtherTrait {
    fn dohtem(&self) -> i32;
}
