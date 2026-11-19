#![flux::opts(allow_raw_deref = "ok")]

// A struct behind a raw pointer is unfolded by a field access through the pointer, and must be
// folded back when the pointer itself is used (e.g. passed to a function).

pub struct S {
    a: usize,
    b: usize,
}

#[flux::spec(fn(*mut S))]
fn takes_folded(p: *mut S) {
    let _ = p;
}

#[flux::spec(fn(*mut S))]
pub unsafe fn pass_after_unfold(p: *mut S) {
    let _x = unsafe { (*p).a };
    takes_folded(p);
}

#[flux::spec(fn(*mut S))]
pub unsafe fn box_from_raw_after_unfold(p: *mut S) {
    if unsafe { (*p).a } == 0 {
        return;
    }
    drop(unsafe { Box::from_raw(p) });
}

// Unfold again after the pointer was folded and passed on
#[flux::spec(fn(*mut S) -> usize)]
pub unsafe fn unfold_fold_unfold(p: *mut S) -> usize {
    let x = unsafe { (*p).a };
    takes_folded(p);
    x + unsafe { (*p).b }
}
