macro_rules! gen_id {
    ($ty:ty) => {
        #[flux_rs::sig(fn(x: $ty) -> $ty[x])]
        pub fn id(x: $ty) -> $ty {
            x
        }
    };
}

gen_id!(i32);

macro_rules! gen_foo {
    ($ty:ty) => {
        #[flux_rs::trusted]
        #[flux_rs::sig(fn(x: $ty) -> Foo<$ty>[0])]
        pub fn foo(x: $ty) -> Foo<$ty> {
            Foo { inner: x }
        }
    };
}

#[flux_rs::opaque]
#[flux_rs::refined_by(n:int)]
struct Foo<T> {
    inner: T,
}

gen_foo!(i32);
