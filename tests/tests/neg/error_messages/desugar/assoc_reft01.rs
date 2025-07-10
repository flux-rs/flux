use flux_rs::attrs::*;

pub trait MyTrait {
    #![assoc(fn f(self: Self) -> bool)]

    fn method(&self) -> i32;
}

#[trusted]
#[sig(fn(n:i32, &{T[@x] | <T as MyTrait>::f(n)}))] //~ ERROR mismatched sorts
pub fn bloo1<T: MyTrait>(_n: i32, x: &T) {
    x.method();
}

#[trusted]
#[sig(fn(n:i32, &{T[@x] | <T as MyTrait>::f(n,n,n)}))] //~ ERROR this function takes 1 refinement argument but 3 were found
pub fn bloo2<T: MyTrait>(_n: i32, x: &T) {
    x.method();
}
