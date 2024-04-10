#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

// We should not check the body of the function
#[flux::trusted]
fn foo() {
    assert(0 > 1);
}
