pub trait MyTrait {
    fn method(&self) -> Self;
}

#[flux::trusted]
#[flux::sig(fn<T as base>(&T{v: <T as MyTrait>::f(v)}) -> T{v: <T as MyTrait>::f(v)})] //~ ERROR associated predicate `f` is not a member of trait `MyTrait`
pub fn lib<T: MyTrait>(x: &T) -> T {
    x.method()
}
