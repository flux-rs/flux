#![feature(step_trait)]
#![allow(unused)]

extern crate flux_core;
use flux_rs::*;

#[flux_rs::sig(fn (bool[true]))]
fn assert(b: bool) {}

#[refined_by(val: int)]
pub struct MyNumber(#[field(i32[val])] i32);

#[assoc(fn into_val(x: MyNumber, y: int) -> bool { x.val == y })]
impl TryInto<i32> for MyNumber {
    type Error = ();

    #[spec(fn(self: MyNumber[@s]) -> Result<i32[s.val], Self::Error>)]
    fn try_into(self) -> Result<i32, Self::Error> {
        Ok(self.0)
    }
}

#[spec(fn (thing: T) -> i32{v: T::into_val(thing, v)})]
fn foo<T: TryInto<i32>>(thing: T) -> i32
where
    <T as TryInto<i32>>::Error: std::fmt::Debug,
{
    let res = thing.try_into().unwrap();
    res
}

fn bar() {
    let my_num = MyNumber(42);
    let n: i32 = foo(my_num);
    assert(n == 42);
}
