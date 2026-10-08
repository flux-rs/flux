#![flux::defs {
    fn mod33(n:int) -> int {
        n % 33
    }

    fn foo(n:int, k:int) -> bool {
        n % 33 == k
    }
}]

#[flux::sig(fn (a:i32) requires foo(a, 7))]
pub fn assert_foo(_a: i32) {}

// `foo` doesn't call `mod33`, so hiding `mod33` doesn't affect it
#[flux::hide(mod33)]
pub fn use_foo(n: i32) {
    if n == 40 {
        assert_foo(n);
    }
}

#[flux::hide(foo)]
#[flux::sig(fn (xs: &[i32{v: foo(v, 7)}][100]) -> i32{v : foo(v, 7)})]
pub fn bar(xs: &[i32]) -> i32 {
    xs[0] // `foo` as uninterpreted works fine
}
