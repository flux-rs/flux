use flux_rs::extern_spec;

pub trait MyTrait {
    fn foo() -> i32;
}

pub trait OtherTrait {
    fn foo() -> i32;
}

// "existing" impl
impl<T> MyTrait for Vec<T> {
    fn foo() -> i32 {
        10
    }
}
impl<T> OtherTrait for Vec<T> {
    fn foo() -> i32 {
        10
    }
}

// "extern" impl
#[extern_spec]
impl<T> MyTrait for Vec<T> {
    #[flux::sig(fn() -> i32[10])]
    fn foo() -> i32;
}

#[flux::sig(fn () -> i32[0])]
pub fn test_bad() -> i32 {
    <Vec<i32> as MyTrait>::foo()
} //~ ERROR refinement type

#[flux::sig(fn () -> i32[10])]
pub fn test_ok() -> i32 {
    <Vec<i32> as MyTrait>::foo()
}
