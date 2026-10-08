#![flux::defs {
    fn mod33(n:int) -> int {
        n % 33
    }

    fn foo(n:int, k:int) -> bool {
        mod33(n) == k
    }
}]

#[flux::sig(fn (a:i32) requires foo(a, 7))]
pub fn assert_foo(_a: i32) {}

pub fn use_foo1(n: i32) {
    if n == 40 {
        assert_foo(n);
    }
}

#[flux::hide(foo)]
pub fn use_foo2(n: i32) {
    if n == 40 {
        assert_foo(n); //~ ERROR refinement type
    }
}

// `foo` calls `mod33`, so hiding `mod33` makes `foo` useless
#[flux::hide(mod33)]
pub fn use_foo3(n: i32) {
    if n == 40 {
        assert_foo(n); //~ ERROR refinement type
    }
}
