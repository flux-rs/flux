#[flux::generics(Self as base)]
#[flux::assoc(fn f(self: Self) -> bool)]
pub trait MyTrait {
    #[flux::sig(fn(self: &Self{v: <Self as MyTrait>::f(v)}) -> Self{v: <Self as MyTrait>::f(v)})]
    fn method(&self) -> Self;
}

#[flux::sig(fn<T as base>(&T{v: <T as MyTrait>::f(v)}) -> T{v: <T as MyTrait>::f(v)})]
pub fn lib<T: MyTrait>(x: &T) -> T {
    x.method()
}

#[flux::sig(fn<T as base>(&T{v: <T as MyTrait>::f(v)}) -> T{v: <T as MyTrait>::f(v)})]
pub fn cli<T: MyTrait>(x: &T) -> T {
    lib(x)
}

#[flux::sig(fn<T as base>(&T) -> T{v: <T as MyTrait>::f(v)})]
pub fn cli2<T: MyTrait>(x: &T) -> T {
    lib(x) //~ ERROR refinement type error
}
