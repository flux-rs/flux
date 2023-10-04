#[flux::sig(fn(bool[true]))]
pub fn assert(_: bool) {}

#[flux::sig(fn(b:bool) ensures b)]
pub fn assume(b: bool) {
    if !b {
        panic!("assume fails")
    }
}

#[flux::sig(fn(x:i32))]
pub fn dec(x: i32) {
    assume(x > 10);
    assert(x > 0);
    assert(x > 20); //~ ERROR refinement type
}

#[flux::sig(fn(b: bool) ensures b)]
pub fn bad_assume(b: bool) {
    if b {
        panic!("assume fails");
    } //~ ERROR refinement type
}
