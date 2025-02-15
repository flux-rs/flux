#[flux::generics(Self as base)]
#[flux::assoc(fn f(self: Self) -> bool)]
pub trait MyTrait {
    fn method(&self) -> i32;
}

impl MyTrait for u32 {
    //~^ ERROR associated refinement `f` is missing from implementation
    fn method(&self) -> i32 {
        10
    }
}
