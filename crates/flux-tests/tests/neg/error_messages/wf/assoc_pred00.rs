#[flux::generics(Self as base)]
#[flux::predicate{ f : (Self) -> bool }]
pub trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::predicate{ f = |x:int| { 1 + x } }] //~ ERROR mismatched sorts
impl MyTrait for i32 {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::predicate{ f = |p:bool| { p } }] //~ ERROR implemented associated predicate `f` has an incompatible sort for trait
impl MyTrait for i16 {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::predicate{ f = |x:int, y:int| { y < x } }] //~ ERROR implemented associated predicate `f` has an incompatible sort for trait
impl MyTrait for i64 {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::predicate{ g = |x:int| { 0 < x } }] //~ ERROR associated predicate `g` is not a member of trait `MyTrait`
impl MyTrait for u32 {
    fn method(&self) -> i32 {
        10
    }
}
