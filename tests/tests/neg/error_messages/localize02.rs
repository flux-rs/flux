#![allow(unused)]
#![flux::defs {
    fn funky(x: int) -> bool {
        0 < x && (x < 10 && x % 2 == 0) //~ NOTE this is the condition
    }

    fn chunky(y:int) -> bool {
        funky(y) && 2 <= y
    }

    fn inc1(x: int) -> int {
        x + 1
    }
}]

// NOTE: This test fails when we run with `FLUX_SMT_DEFINE_FUN=1`
// as errors are reported in some other place than shown below.

#[flux::sig(fn(x: i32{ chunky(x) }))] //~ NOTE inside this call
fn assertp(_x: i32) {}

fn test() {
    assertp(12); //~ ERROR refinement type
                 //~| NOTE a precondition cannot be proved
}

#[flux::sig(fn() -> i32[inc1(0)])] //~ NOTE this is the condition
fn moo() -> i32 {
    2 //~ ERROR refinement type
      //~| NOTE a postcondition cannot be proved
}
