#[flux::sig(fn(bool[true]))]

fn assert(_: bool) {}
#[flux::sig(
    fn(x: i32)
    requires forall y. y >= 0 => y > x
)]
fn requires_negative(x: i32) {
    assert(x + 1 == 1 + x); // make sure there's something to check to avoid optimizing the entire constraint away
}

fn test2() {
    requires_negative(-1);
}
