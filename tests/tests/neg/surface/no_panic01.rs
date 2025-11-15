pub fn this_might_panic() -> i32 {
    let v = vec![1, 2, 3];
    v[0]
}

#[cfg_attr(flux, flux::no_panic)]
mod my_module {
    use super::this_might_panic;
    trait MyTrait {
        fn do_something(&self) -> i32;
    }

    struct MyStruct;
    impl MyTrait for MyStruct {
        fn do_something(&self) -> i32 {
            this_might_panic() //~ ERROR may panic
        }
    }
}
