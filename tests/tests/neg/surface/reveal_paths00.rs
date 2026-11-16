// Test that revealing through a path is needed, i.e., the reveal in `reveal_paths00` is not vacuous

pub mod defs {
    use flux_attrs::*;

    defs! {
        #[hide]
        fn mod33(n: int) -> int {
            n % 33
        }

        #[hide]
        fn foo(n: int, k: int) -> bool {
            mod33(n) == k
        }

        fn bar(n: int) -> bool {
            n > 0
        }
    }

    #[spec(fn(a: i32) requires foo(a, 7))]
    pub fn assert_foo(_a: i32) {}

    #[spec(fn(a: i32) requires bar(a))]
    pub fn assert_bar(_a: i32) {}
}

#[flux::reveal(defs::foo)]
pub fn use_foo_missing_mod33(n: i32) {
    if n == 40 {
        defs::assert_foo(n) //~ ERROR refinement type
    }
}

#[flux::hide(defs::bar)]
pub fn hide_bar(n: i32) {
    if n > 0 {
        defs::assert_bar(n) //~ ERROR refinement type
    }
}
