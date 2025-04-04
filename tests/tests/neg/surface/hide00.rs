#![flux::defs {
    hide
    fn mod33(n:int) -> int {
        n % 33
    }

    hide
    fn foo(n:int, k:int) -> bool {
      mod33(n) == k
    }

}]

#[flux::sig(fn (a:i32) requires foo(a, 7))]
pub fn assert_foo(_a: i32) {}

#[flux::reveal(foo, mod33)]
pub fn use_foo1(n: i32) {
    if n == 40 {
        assert_foo(n)
    }
}

#[flux::reveal(mod33)]
pub fn use_foo2(n: i32) {
    if n == 40 {
        assert_foo(n) //~ ERROR: refinement type
    }
}

#[flux::reveal(foo)]
pub fn use_foo3(n: i32) {
    if n == 40 {
        assert_foo(n) //~ ERROR: refinement type
    }
}

pub fn use_foo4(n: i32) {
    if n == 40 {
        assert_foo(n) //~ ERROR: refinement type
    }
}

#[flux::sig(fn (xs: &[i32{v: foo(v, 7)}][100]) -> i32{v : foo(v, 7)})]
pub fn bar(xs: &[i32]) -> i32 {
    xs[0] // `foo` as uninterpreted works fine
}
