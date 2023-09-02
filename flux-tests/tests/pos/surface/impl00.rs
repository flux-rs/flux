#![feature(register_tool)]
#![register_tool(flux)]

pub trait MyTrait {
    fn foo(x: i32);
}

pub struct MyTy;

impl MyTrait for MyTy {
    fn foo(_x: i32) {}
}

pub fn test() {
    MyTy::foo(10)
}
