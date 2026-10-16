// Mutable raw pointers are invariant in their pointee, so joining two `*mut` whose
// pointees have different indices cannot be generalized to a common type.

#[flux::trusted]
#[flux::sig(fn(n: usize) -> *mut ([i32][n]))]
fn alloc(n: usize) -> *mut [i32] {
    std::ptr::slice_from_raw_parts_mut(std::ptr::null_mut(), n)
}

#[flux::sig(fn() -> usize{v: v > 0})]
fn len() -> usize {
    1
}

#[flux::sig(fn(bool[@b]) -> *mut[#p] [i32]{v : v > 0})]
pub fn test00(b: bool) -> *mut [i32] {
    let p;
    if b { //~ ERROR error jumping to join point
        p = alloc(len());
    } else { //~ ERROR error jumping to join point
        p = alloc(1);
    }
    p
}
