#![allow(dead_code)]

use flux_rs::attrs::*;

trait MyTrait {
    #![reft(fn f(x: int) -> int)]
    //
}

struct Add1;

impl MyTrait for Add1 {
    #![reft(fn f(x: int) -> int { x + 1 })]
    //
}

#[sig(fn(x: i32{v: v == <Add1 as MyTrait>::f(0) }))]
fn test00(_x: i32) {}

fn test01() {
    test00(1);
}
