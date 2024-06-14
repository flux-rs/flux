#[flux::generics(Self as base)]
#[flux::assoc(fn f(self: Self) -> bool)]
pub trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::assoc(fn g(x:int) -> bool { 0 < x } )] //~ ERROR associated refinement `g` is not a member of trait `MyTrait`
impl MyTrait for u32 {
    fn method(&self) -> i32 {
        10
    }
}
