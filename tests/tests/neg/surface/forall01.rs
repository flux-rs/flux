#[flux::sig(fn(bool[true]))]

fn assert(_: bool) {}
#[flux::sig(
    fn(x: i32)
    requires forall y. y >= 0 => y > x
)]
fn requires_negative(x: i32) {
    // this should be provable, but we are currently dropping the quantified assumption
    assert(x <= 0); //~ ERROR refinement type
}

fn test2() {
    requires_negative(0); //~ ERROR refinement type
}
