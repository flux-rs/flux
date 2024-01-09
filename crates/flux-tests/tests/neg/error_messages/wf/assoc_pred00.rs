#[flux::generics(Self as base)]
#[flux::predicate{ f : (Self) -> bool }]
trait MyTrait {
    fn method(&self) -> i32;
}

#[flux::predicate{ f : |x:int| { 1 + x } }] //~ ERROR mismatched sorts
impl MyTrait for i32 {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::predicate{ f : |x:int, y:int| { y < x } }] // TODO: check-against-trait
impl MyTrait for usize {
    fn method(&self) -> i32 {
        10
    }
}

#[flux::predicate{ g : |x:int| { 0 < x } }] // TODO: check-against-trait
impl MyTrait for u32 {
    fn method(&self) -> i32 {
        10
    }
}
