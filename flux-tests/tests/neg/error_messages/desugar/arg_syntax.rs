#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(x: i32{v: v > 0 && v < 10}) -> i32[x])] //~ ERROR invalid use of refinement parameter
fn exists(x: i32) -> i32 {
    x
}

#[flux::sig(fn(x: &mut i32) -> i32[x])] //~ ERROR invalid use of refinement parameter
fn mut_ref(x: &mut i32) -> i32 {
    *x
}

#[flux::sig(fn(x: &i32) -> i32[x])] //~ ERROR invalid use of refinement parameter
fn shr_ref(x: &i32) -> i32 {
    *x
}
