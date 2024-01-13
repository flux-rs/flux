#[flux::generics(Self as base)]
#[flux::predicate{ f : (Self) -> bool }]
pub trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::predicate{ f : |x:int| { 1 + x } }] //~ ERROR mismatched sorts
impl MyTrait for i32 {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::predicate{ f : |p:bool| { p } }] //~ ERROR mismatched sorts
impl MyTrait for i16 {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::predicate{ f : |x:int, y:int| { y < x } }] //~ ERROR this associated predicate takes 1 refinement argument but 2 were found
impl MyTrait for i64 {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::predicate{ g : |x:int| { 0 < x } }] //~ ERROR invalid associated predicate `g`
impl MyTrait for u32 {
    fn method(&self) -> i32 {
        10
    }
}
