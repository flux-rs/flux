#[flux::generics(Self as base)]
#[flux::assoc(fn f(self: Self) -> bool)]
pub trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::trusted]
#[flux::sig(fn<T as base>(n:i32, &{T[@x] | <T as MyTrait>::f(n)}))] //~ ERROR mismatched sorts
pub fn bloo1<T: MyTrait>(_n: i32, x: &T) {
    x.method();
}

#[flux::trusted]
#[flux::sig(fn<T as base>(n:i32, &{T[@x] | <T as MyTrait>::f(n,n,n)}))] //~ ERROR this function takes 1 refinement argument but 3 were found
pub fn bloo2<T: MyTrait>(_n: i32, x: &T) {
    x.method();
}
