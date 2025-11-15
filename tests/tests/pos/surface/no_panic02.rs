#[cfg_attr(flux, flux::no_panic)]
mod my_module {
    trait MyTrait {
        fn do_something(&self) -> i32;
    }

    struct MyStruct;
    impl MyTrait for MyStruct {
        fn do_something(&self) -> i32 {
            42
        }
    }
}