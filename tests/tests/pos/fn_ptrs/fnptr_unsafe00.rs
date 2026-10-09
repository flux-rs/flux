// Specs for `unsafe` and `extern` fn pointers

#[flux::refined_by(n: int)]
pub struct Handle {
    #[flux::field(usize[n])]
    n: usize,
}

#[flux::refined_by()]
pub struct UnsafeVtable {
    #[flux::field(unsafe fn(&Handle[@h]) -> Handle[h])]
    clone: unsafe fn(&Handle) -> Handle,
}

#[flux::spec(fn(&UnsafeVtable, &Handle[@h]) -> Handle[h])]
pub unsafe fn via_unsafe_field(vt: &UnsafeVtable, h: &Handle) -> Handle {
    unsafe { (vt.clone)(h) }
}

#[flux::refined_by()]
pub struct ExternVtable {
    #[flux::field(extern "C" fn(usize[@n]) -> usize[n + 1])]
    inc: extern "C" fn(usize) -> usize,
    #[flux::field(unsafe extern "C" fn(usize[@n]) -> usize[n])]
    id: unsafe extern "C" fn(usize) -> usize,
    // `extern fn` is `extern "C" fn`
    #[flux::field(extern fn(usize[@n]) -> usize[n])]
    id2: extern "C" fn(usize) -> usize,
}

#[flux::spec(fn(&ExternVtable, x: usize) -> usize[x + 1])]
pub fn via_extern(vt: &ExternVtable, x: usize) -> usize {
    (vt.inc)(x)
}

#[flux::spec(fn(&ExternVtable, x: usize) -> usize[x])]
pub unsafe fn via_unsafe_extern(vt: &ExternVtable, x: usize) -> usize {
    unsafe { (vt.id)(x) }
}

#[flux::spec(fn(&ExternVtable, x: usize) -> usize[x])]
pub fn via_extern_default(vt: &ExternVtable, x: usize) -> usize {
    (vt.id2)(x)
}
