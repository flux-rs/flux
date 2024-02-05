// use flux_rs::extern_spec;

// Trait with assoc-pred
#[flux::predicate{ f : (int) -> bool }]
pub trait MyTrait {
    fn foo() -> i32;
}

// Function that uses assoc-pred generically
#[flux::trusted]
#[flux::sig(fn (_x:&T) -> i32{v: <T as MyTrait>::f(v)})]
pub fn bob<T: MyTrait>(_x: &T) -> i32 {
    <T as MyTrait>::foo()
}

impl MyTrait for usize {
    #[flux::trusted]
    fn foo() -> i32 {
        10
    }
}

#[allow(dead_code)]
struct __FluxExternStruct1usize();

#[allow(dead_code, unused_variables)]
#[flux::extern_spec]
#[flux::predicate{ f = |x:int| { 10 < x } }]
impl __FluxExternStruct1usize {
    #[flux::fake_impl]
    fn __flux_extern_impl_fake_method<FluxFake: MyTrait>(x: usize) {}
}

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
