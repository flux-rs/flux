// A raw pointer whose pointee is refined by a variable local to a branch must be
// generalized when the branches join. In `test00` the first edge into the join has a
// closed pointee and the second one has a free var (exercises `join_bty`); in `test01` it
// is the other way around (exercises `pack_bty`).

#[flux::trusted]
#[flux::sig(fn(n: usize) -> *const ([i32][n]))]
fn alloc(n: usize) -> *const [i32] {
    std::ptr::slice_from_raw_parts(std::ptr::null(), n)
}

#[flux::sig(fn() -> usize{v: v > 0})]
fn len() -> usize {
    1
}

#[flux::sig(fn(bool) -> *const ([i32]{n: n > 0}))]
pub fn test00(b: bool) -> *const [i32] {
    let p;
    if b {
        p = alloc(len());
    } else {
        p = alloc(1);
    }
    p
}

#[flux::sig(fn(bool) -> *const ([i32]{n: n > 0}))]
pub fn test01(b: bool) -> *const [i32] {
    let p;
    if b {
        p = alloc(1);
    } else {
        p = alloc(len());
    }
    p
}
