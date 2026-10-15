// We only infer the refinement of a generic parameter if it occurs negatively in the signature
// of the callee. A parameter that only occurs positively is instantiated with a trivial
// refinement, otherwise nothing would constrain it and we would infer `false`.

use std::ptr::NonNull;

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

#[flux::trusted]
fn conjure<T>() -> T {
    loop {}
}

pub fn test_conjure() {
    let x: i32 = conjure();
    if x > 99 {
        assert(false); //~ ERROR refinement type
    }
}

// `U` only occurs in the output of `NonNull::cast`
pub unsafe fn test_non_null(p: NonNull<()>) {
    let p: NonNull<i32> = p.cast();
    let x = *p.as_ref();
    if x > 99 {
        assert(false); //~ ERROR refinement type
    }
}

// `A` occurs in an input, but under the input of a `fn`, so it only occurs positively
#[flux::trusted]
fn pos_under_fn<A>(_f: fn(A)) -> A {
    loop {}
}

fn eat(_x: i32) {}

pub fn test_pos_under_fn() {
    let x = pos_under_fn(eat as fn(i32));
    if x > 99 {
        assert(false); //~ ERROR refinement type
    }
}
