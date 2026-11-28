struct S {
    exp: i32,
}

impl S {
    fn shr(&mut self, _shift: i32) {}

    #[flux::sig(fn(self: &strg S, i32) ensures self: S)]
    fn strong(&mut self, _value: i32) {}

    fn borrow(&mut self, _value: i32) -> &mut S {
        self
    }
}

fn original(b: &mut S) {
    b.shr(b.exp);
    b.exp = 0;
}

// Activation must emit a fold, not just update the analysis state.
fn strong_receiver(b: &mut S) {
    b.strong(b.exp);
    b.exp = 0;
}

struct Outer {
    inner: S,
}

// The returned loan must end before unfolding the receiver for its field write.
fn returned_receiver(b: &mut Outer) {
    let r = b.inner.borrow(b.inner.exp);
    r.exp = 0;
    b.inner.exp = 1;
}
