trait Trait {
    #[flux::sig(fn(&Self) -> i32{v: v >= 0})]
    fn foo(&self) -> i32;
}

#[flux::sig(fn(T) -> i32{v: v > 0})]
fn baz<T: Trait>(x: T) -> i32 {
    x.foo()
} //~ ERROR refinement type error
