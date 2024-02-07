use flux_rs::extern_spec;

// Trait with assoc-pred
#[flux::assoc(fn f(x: int) -> bool )]
pub trait MyTrait {
    fn foo() -> i32;
}

// Function that uses assoc-pred generically
#[flux::trusted]
#[flux::sig(fn (_x:&T) -> i32{v: <T as MyTrait>::f(v)})]
pub fn bob<T: MyTrait>(_x: &T) -> i32 {
    <T as MyTrait>::foo()
}

// library impl
impl MyTrait for usize {
    #[flux::trusted]
    fn foo() -> i32 {
        10
    }
}

// extern impl
#[extern_spec]
#[flux::assoc(fn f(x: int) -> bool { 10 < x } )]
impl MyTrait for usize {}

#[flux::sig(fn () -> i32{v: 100 < v})]
pub fn test_fail() -> i32 {
    let u: usize = 0;
    bob(&u) //~ ERROR refinement type
}

#[flux::sig(fn () -> i32{v: 10 < v})]
pub fn test_ok() -> i32 {
    let u: usize = 0;
    bob(&u)
}
