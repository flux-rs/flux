//@no-prefer-dynamic

// Trait with assoc-pred
#[flux::assoc(fn f(x: int) -> bool)]
pub trait MyTrait {
    fn foo() -> i32;
}

#[flux::trusted]
#[flux::sig(fn (_x:&T) -> i32{v: <T as MyTrait>::f(v)})]
pub fn bob<T: MyTrait>(_x: &T) -> i32 {
    <T as MyTrait>::foo()
}

#[flux::ignore]
impl MyTrait for usize {
    fn foo() -> i32 {
        10
    }
}
