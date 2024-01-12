#[flux::generics(Self as base)]
#[flux::predicate{ f : (Self) -> int }] //~ ERROR invalid associated predicate
pub trait OtherTrait {
    fn method(&self) -> i32;
}
