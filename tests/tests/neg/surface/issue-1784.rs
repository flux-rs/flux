// Join points right after an empty `if` (see #1784).

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

pub fn test1(b: bool) -> i32 {
    let mut i = 0;
    if b {}
    while i < 10 {
        i += 1;
    }
    assert(i > 100); //~ ERROR refinement type
    i
}
