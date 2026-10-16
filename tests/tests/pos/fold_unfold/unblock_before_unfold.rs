struct S {
    exp: i32,
}

impl S {
    fn borrow(&mut self, _value: i32) -> &mut S {
        self
    }
}

fn returned_receiver(b: &mut S) {
    let r = b.borrow(b.exp);
    r.exp = 0;
    b.exp = 1;
}

// The loan-end ordering matters independently of two-phase argument reads.
fn constant_argument(b: &mut S) {
    let r = b.borrow(0);
    r.exp = 0;
    b.exp = 1;
}

struct Outer {
    inner: S,
    other: S,
}

impl Outer {
    fn borrow_inner(&mut self, _value: i32) -> &mut S {
        &mut self.inner
    }
}

fn returned_field(b: &mut Outer) {
    let r = b.borrow_inner(b.other.exp);
    r.exp = 0;
    b.other.exp = 1;
}

fn nested_receiver(b: &mut Outer) {
    let r = b.inner.borrow(b.inner.exp);
    r.exp = 0;
    b.inner.exp = 1;
}
