// The refinements on the pointee of a raw pointer are not trusted: a raw pointer can be created
// without a value of the pointee type, so we must not assume anything about what we read from it.

#[flux::spec(fn (bool[true]))]
fn assert(_b: bool) {}

// `cast` produces a `*mut U` for any `U`, the read must not see a `U` refined by `false`.
pub unsafe fn cast_then_deref(shared: *mut ()) {
    let shared: *mut i32 = shared.cast();
    let foo = *shared;
    if foo > 99 {
        assert(false); //~ ERROR refinement type
    }
}

#[flux::trusted]
unsafe fn read<T>(p: *const T) -> T {
    unsafe { p.read() }
}

// Same thing but reading through a function instead of a place.
pub unsafe fn cast_then_read(shared: *const ()) {
    let shared: *const i32 = shared.cast();
    let foo = read(shared);
    if foo > 99 {
        assert(false); //~ ERROR refinement type
    }
}

#[flux::spec(fn (p: *mut i32{v: v > 0}) -> i32{v: v > 0})]
pub unsafe fn refined_pointee(p: *mut i32) -> i32 {
    *p //~ ERROR refinement type
}
