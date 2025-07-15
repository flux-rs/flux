pub struct S {}

#[flux::sig(fn(x:S) -> i32[cast(x)])] //~ ERROR invalid cast
pub fn foo(_x: S) -> i32 {
    0
}
