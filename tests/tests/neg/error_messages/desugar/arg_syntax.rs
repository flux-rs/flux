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

// ensures clause on non-strong reference
#[flux::sig(fn(x: &mut i32[@n]) ensures x: i32[n+1])] //~ ERROR invalid use of refinement parameter
pub fn test00(x: &mut i32) {
    *x += 1;
    return;
}
