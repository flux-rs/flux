use flux_rs::attrs::*;

trait MyTrait {
    #![reft(fn f(x: int) -> int)]
    //
}

struct Add1;

#[assoc(fn f(x: int) -> int { x + 1 })]
impl MyTrait for Add1 {}

#[sig(fn(x: i32{v: v == <Add1 as MyTrait>::f(0) }))]
fn test00(x: i32) {}

fn test01() {
    test00(0); //~ ERROR refinement type error
}
