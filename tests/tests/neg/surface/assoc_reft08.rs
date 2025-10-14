// Test we normalize the sorts of associated refinements during sort checking

use flux_rs::attrs::*;

#[assoc(fn foo(x: Self::Assoc) -> bool)]
trait MyTrait {
    type Assoc;
}

struct S;

#[assoc(fn foo(x: int) -> bool { x > 0 })]
impl MyTrait for S {
    type Assoc = i32;
}

#[spec(fn(x: <S as MyTrait>::Assoc{v: <S as MyTrait>::foo(v) }))]
fn test00(x: <S as MyTrait>::Assoc) {}

fn test01() {
    test00(0); //~ERROR refinement type error
}
