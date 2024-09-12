#![allow(dead_code)]

#[flux::assoc(fn f(x: int) -> int)]
trait MyTrait {}

struct Add1;

#[flux::assoc(fn f(x: int) -> int { x + 1 })]
impl MyTrait for Add1 {}

#[flux::sig(fn(x: i32{v: v == <Add1 as MyTrait>::f(0) }))]
fn test00(_x: i32) {}

fn test01() {
    test00(1);
}
