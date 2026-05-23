#[flux_rs::trusted_impl]
pub mod foo {

    pub trait Bar {
        #[flux_rs::sig(fn (&Self) -> i32{v:100 <= v})]
        fn baz(&self) -> i32;
    }

    impl Bar for u32 {
        fn baz(&self) -> i32 {
            12
        }
    }
}
