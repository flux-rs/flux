// Test that `#[reveal(...)]` and `#[hide(...)]` accept paths to function definitions

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

    pub mod nested {
        #[flux_attrs::reveal(super::foo, super::mod33)]
        pub fn use_foo_super(n: i32) {
            if n == 40 {
                super::assert_foo(n)
            }
        }
    }
}

#[flux::reveal(defs::foo, defs::mod33)]
pub fn use_foo(n: i32) {
    if n == 40 {
        defs::assert_foo(n)
    }
}

#[flux::reveal(crate::defs::foo, crate::defs::mod33)]
pub fn use_foo_crate(n: i32) {
    if n == 40 {
        defs::assert_foo(n)
    }
}

#[flux::hide(defs::bar)]
#[flux::sig(fn(xs: &[i32{v: defs::bar(v)}][100]))]
pub fn hide_bar(xs: &[i32]) {
    defs::assert_bar(xs[0]) // `bar` as uninterpreted works fine
}
