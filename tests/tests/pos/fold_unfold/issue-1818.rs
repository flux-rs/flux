// A two-phase receiver borrow is reserved before its arguments are evaluated.
// Reading a field in an argument unfolds the receiver again; activation must
// fold it before the call so later projections unfold it consistently.
struct S {
    exp: i32,
    other: i32,
}

impl S {
    fn shr(&mut self, _shift: i32) {}

    fn set(&mut self, value: i32) {
        self.exp = value;
    }

    #[flux::sig(fn(self: &strg S, i32) ensures self: S)]
    fn strong(&mut self, _value: i32) {}
}

fn original(b: &mut S) {
    b.shr(b.exp);
    b.exp = 0;
}

fn owned(mut b: S) {
    b.shr(b.exp);
    b.exp = 0;
}

fn sibling(b: &mut S) {
    b.shr(b.exp);
    b.other = 0;
}

struct Outer {
    inner: S,
}

fn nested(b: &mut Outer) {
    b.inner.shr(b.inner.exp);
    b.inner.exp = 0;
}

fn mutating(b: &mut S) {
    b.set(b.exp);
    b.exp = 0;
}

fn strong_receiver(b: &mut S) {
    b.strong(b.exp);
    b.exp = 0;
}

fn repeated(b: &mut S) {
    b.shr(b.exp);
    b.exp = 0;
    b.shr(b.exp);
    b.other = 0;
}

fn join(b: &mut S, cond: bool) {
    if cond {
        b.shr(b.exp);
    }
    b.exp = 0;
}

fn loop_backedge(b: &mut S, mut cond: bool) {
    while cond {
        b.shr(b.exp);
        b.exp = 0;
        cond = false;
    }
}
