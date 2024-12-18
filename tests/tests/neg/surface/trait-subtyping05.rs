// Test that trait subtyping is checked even if function is trusted

trait MyTrait {
    #[flux::sig(fn() -> i32{v: v > 0})]
    fn test00() -> i32;
}

struct S;

impl MyTrait for S {
    #[flux::trusted]
    #[flux::sig(fn() -> i32{v: v >= 0})] //~ ERROR refinement type error
    fn test00() -> i32 {
        1 - 1
    }
}
