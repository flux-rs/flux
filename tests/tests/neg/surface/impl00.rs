pub trait MyTrait {
    fn foo() -> i32;
    fn bar();
}

pub struct MyTy;

impl MyTrait for MyTy {
    #[flux::sig(fn () -> i32[10])]
    fn foo() -> i32 {
        1 //~ ERROR refinement type
    }

    fn bar() {}
}

#[flux::sig(fn () -> i32[100])]
pub fn test() -> i32 {
    let n = MyTy::foo();
    MyTy::bar();
    n //~ ERROR refinement type
}
