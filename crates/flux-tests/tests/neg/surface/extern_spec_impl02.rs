// use flux_rs::extern_spec;

// Trait with assoc-pred
#[flux::predicate{ f : (int) -> bool }]
pub trait MyTrait {
    fn foo() -> i32;
}

// Function that uses assoc-pred generically
#[flux::trusted]
#[flux::sig(fn (x:&T) -> i32{v: <T as MyTrait>::f(v)})]
pub fn bob<T: MyTrait>(_x: &T) -> i32 {
    <T as MyTrait>::foo()
}

// #[flux::predicate{ f = |x:int| { 10 < x } }]
impl MyTrait for usize {
    #[flux::trusted]
    fn foo() -> i32 {
        10
    }
}

// extern impl
// #[extern_spec]
// #[flux::predicate{ f = |x:int| { 10 < x } }]
// impl MyTrait for usize {}

#[allow(dead_code)]
struct __FluxExternStruct1usize();

#[allow(dead_code)]
#[flux::predicate{ f = |x:int| { 10 < x } }]
impl __FluxExternStruct1usize {
    // #[flux::use_me_to_determine_impl_id]
    #[allow(unused_variables)]
    fn __flux_extern_impl_fake_method<A: MyTrait>(x: usize) {}
}

// test

#[flux::sig(fn () -> i32{v: 100 < v})]
pub fn test_fail() -> i32 {
    let z: usize = 99;
    bob(&z) //~ ERROR refinement type
}

#[flux::sig(fn () -> i32{v: 10 < v})]
pub fn test_ok() -> i32 {
    let z: usize = 99;
    bob(&z)
}
