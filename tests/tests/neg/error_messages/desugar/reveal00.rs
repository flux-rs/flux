#![flux::defs {
    #[hide]
    fn mod33(n:int) -> int {
        n % 33
    }

    #[hide]
    fn foo(n:int, k:int) -> bool {
      mod33(n) == k
    }

}]

#[flux::sig(fn (a:i32) requires foo(a, 7))]
pub fn assert_foo(_a: i32) {}

#[flux::reveal(fool)] //~ ERROR unknown function definition
pub fn use_foo(n: i32) {}

#[flux::sig(fn (xs: &[i32{v: foo(v, 7)}][100]) -> i32{v : foo(v, 7)})]
pub fn bar(xs: &[i32]) -> i32 {
    xs[0] // `foo` as uninterpreted works fine
}
