#![allow(unused)]
extern crate flux_core;
use flux_rs::*;

#[refined_by(val: int)]
pub struct MyNumber {
    #[field(i32[val])]
    val: i32,
}

#[assoc(fn from_val(x: int, y: MyNumber) -> bool { x == y.val })]
impl TryFrom<i32> for MyNumber {
    type Error = ();

    #[spec(fn(i32[@x]) -> Result<MyNumber{v: x == v.val}, Self::Error>[true])]
    fn try_from(value: i32) -> Result<Self, Self::Error> {
        Ok(MyNumber { val: value })
    }
}

// concrete test: value flows through try_from into the Ok payload
pub fn test_try_from_concrete() {
    let r: Result<MyNumber, ()> = MyNumber::try_from(42);
    let m = r.unwrap();
    assert(m.val == 42);
}

// generic function that exposes from_val in its postcondition
#[spec(fn (x: i32) -> T{v: <T as TryFrom<i32>>::from_val(x, v)})]
fn foo<T: TryFrom<i32>>(x: i32) -> T
where
    <T as TryFrom<i32>>::Error: std::fmt::Debug,
{
    match T::try_from(x) {
        Ok(v) => v,
        Err(e) => panic!("{:?}", e),
    }
}

// caller can recover the concrete from_val predicate for MyNumber
pub fn bar() {
    let my_num: MyNumber = foo(42);
    assert(my_num.val == 42);
}
