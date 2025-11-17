#[cfg_attr(flux, flux::no_panic)]
mod my_other_module {
    pub fn this_wont_panic() -> i32 {
        3
    }
}


#[cfg_attr(flux, flux::no_panic)]
mod my_module {
    use super::my_other_module;
    trait MyTrait {
        fn do_something(&self) -> i32;
    }

    struct MyStruct;
    impl MyTrait for MyStruct {
        fn do_something(&self) -> i32 {
            my_other_module::this_wont_panic()
        }
    }
}
