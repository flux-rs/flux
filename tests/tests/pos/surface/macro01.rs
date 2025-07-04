macro_rules! gen_foo {
    ($ty:ty, $desc:ident) => {
        #[flux_rs::trusted]
        #[flux_rs::sig(fn(x: $ty) -> Foo<$desc>[0])]
        pub fn foo(x: $ty) -> Foo<$ty> {
            Foo { _inner: x }
        }
    };
}

#[flux_rs::opaque]
#[flux_rs::refined_by(n:int)]
pub struct Foo<T> {
    _inner: T,
}

gen_foo!(i32, i32);
