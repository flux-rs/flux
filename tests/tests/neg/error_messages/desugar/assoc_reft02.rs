pub trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::trusted]
#[flux::sig(fn<T as base>(&T{v: <T as MyTrait>::f(v)}) -> i32)] //~ ERROR associated refinement `f` is not a member of trait `MyTrait`
pub fn lib<T: MyTrait>(x: &T) -> i32 {
    x.method()
}
