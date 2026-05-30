macro_rules! gen_foo {
    ($desc:ident) => {
        #[flux_rs::sig(fn() -> $desc)]
        pub fn foo() -> $desc {
            0
        }
    };
}

pub struct Foo<T> {
    _inner: T,
}

gen_foo!(i32);
