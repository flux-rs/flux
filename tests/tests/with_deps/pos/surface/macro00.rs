macro_rules! gen_id {
    ($ty:ty) => {
        #[flux_rs::sig(fn(x: $ty) -> $ty[x])]
        pub fn id(x: $ty) -> $ty {
            x
        }
    };
}

gen_id!(i32);
