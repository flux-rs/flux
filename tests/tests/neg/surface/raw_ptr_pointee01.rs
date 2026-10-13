#![flux::opts(allow_raw_deref = "ok")]

// Like `raw_ptr_pointee00.rs` but for a struct that gets unfolded behind the raw pointer.

#[flux::spec(fn (bool[true]))]
fn assert(_b: bool) {}

pub struct S {
    a: usize,
    b: usize,
}

pub unsafe fn cast_then_field(shared: *mut ()) {
    let shared: *mut S = shared.cast();
    let foo = (*shared).a;
    if foo > 99 {
        assert(false); //~ ERROR refinement type
    }
}
