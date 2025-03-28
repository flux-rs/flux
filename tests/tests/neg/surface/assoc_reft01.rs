use flux_rs::attrs::*;

pub trait MyTrait {
    #![reft(fn f(self: Self) -> bool)]

    #[sig(fn(self: &Self{v: <Self as MyTrait>::f(v)}) -> Self{v: <Self as MyTrait>::f(v)})]
    fn method(&self) -> Self;
}

#[sig(fn(&T{v: <T as MyTrait>::f(v)}) -> T{v: <T as MyTrait>::f(v)})]
pub fn lib<T: MyTrait>(x: &T) -> T {
    x.method()
}

#[sig(fn(&T{v: <T as MyTrait>::f(v)}) -> T{v: <T as MyTrait>::f(v)})]
pub fn cli<T: MyTrait>(x: &T) -> T {
    lib(x)
}

#[sig(fn(&T) -> T{v: <T as MyTrait>::f(v)})]
pub fn cli2<T: MyTrait>(x: &T) -> T {
    lib(x) //~ ERROR refinement type error
}
