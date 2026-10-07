#![flux::defs {
    fn foo(n:int, k:int) -> bool {
        n % 33 == k
    }
}]

#[flux::hide(fool)] //~ ERROR unknown function definition
pub fn use_foo(n: i32) {}
