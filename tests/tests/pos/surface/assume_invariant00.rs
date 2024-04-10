//! Test we assume invariants when unfolding

#![flux::cfg(check_overflow = true)]

#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

#[flux::sig(fn(&[i32]{len: len > 0}))]
fn test01(s: &[i32]) {
    assert(s[0] <= i32::MAX);
}

struct S {
    val: u32,
}

// https://github.com/flux-rs/flux/issues/451
impl S {
    fn test02(&mut self) {
        let tmp = self.val;
        if tmp == 0 {
            return;
        }
        let a = tmp - 1;
    }
}
