#[flux::generics(Self as base)]
#[flux::assoc(fn f(self: Self) -> bool)]
pub trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::assoc(fn f(p: bool) -> bool { p } )] //~ ERROR implemented associated refinement `f` has an incompatible sort for trait
impl MyTrait for i16 {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::assoc(fn f(x:int, y:int) -> bool { y < x } )] //~ ERROR implemented associated refinement `f` has an incompatible sort for trait
impl MyTrait for i64 {
    fn method(&self) -> i32 {
        10
    }
}
