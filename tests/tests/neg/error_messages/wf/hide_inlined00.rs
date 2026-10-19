#![flux::defs {
    fn id<T>(x: T) -> T {
        x
    }

    #[hide]
    fn foo(n:int) -> bool {
        n > 0
    }
}]

#[flux::hide(id)] //~ ERROR cannot hide inlined definition
pub fn hide_poly() {}

#[flux::hide(foo)] //~ ERROR both hidden and revealed
#[flux::reveal(foo)]
pub fn hide_and_reveal() {}
