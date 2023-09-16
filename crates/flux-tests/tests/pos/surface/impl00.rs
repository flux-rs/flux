#![feature(register_tool)]
#![register_tool(flux)]

pub trait MyTrait {
    fn foo() -> i32;
    fn bar();
}

pub struct MyTy;

impl MyTrait for MyTy {
    #[flux::sig(fn () -> i32[10])]
    fn foo() -> i32 {
        10
    }

    fn bar() {}
}

#[flux::sig(fn () -> i32[10])]
pub fn test() -> i32 {
    let n = MyTy::foo();
    MyTy::bar();
    n
}
