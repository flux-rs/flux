// #[flux::generics(Self as base)]
// #[flux::predicate{ f : (Self) -> bool }]
// pub trait MyTrait {
//     fn method(&self) -> i32;
// }

// // #[flux::trusted]
// #[flux::sig(fn<T as base>(&{T[@x] | <T as MyTrait>::f(x)}))] // TODO: check against trait-spec
// pub fn bob<T: MyTrait>(x: &T) {
//     x.method();
// }

#[flux::generics(Self as base)]
#[flux::predicate(f: (Self) -> bool)]
trait MyTrait {
    #[flux::sig(fn(self: &Self{v: <Self as MyTrait>::f(v)}) -> Self{v: <Self as MyTrait>::f(v)})]
    fn method(&self) -> Self;
}
// i32{v:p(v)}
// #[flux::sig(fn<T as base>(&T{v: <T as MyTrait>::f(x)}) -> T{v: <T as MyTrait>::f(x)})]
// pub fn bob<T: MyTrait>(x: &T) -> T {
//     x.method()
// }
