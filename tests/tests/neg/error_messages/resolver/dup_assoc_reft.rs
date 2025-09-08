use flux_rs::attrs::*;

#[assoc(
    fn foo() -> bool;
    fn foo() -> bool;  //~ ERROR name `foo` is defined multiple times
)]
trait MyTrait {}

#[assoc(
    fn baz() -> bool { true }
    fn baz() -> bool { true }  //~ ERROR name `baz` is defined multiple times
)]
impl MyTrait for i32 {}
