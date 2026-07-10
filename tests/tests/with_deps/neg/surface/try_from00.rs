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

// from_val says val == x, not x + 1
pub fn test_wrong_value(x: i32) {
    let m: MyNumber = MyNumber::try_from(x).unwrap();
    assert(m.val == x + 1); //~ ERROR refinement type error
}

// generic function returning T{v: from_val(x, v)}
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

// caller asserts a stronger property than from_val alone can guarantee
pub fn test_generic_wrong_value() {
    let my_num: MyNumber = foo(42);
    assert(my_num.val == 0); //~ ERROR refinement type error
}
