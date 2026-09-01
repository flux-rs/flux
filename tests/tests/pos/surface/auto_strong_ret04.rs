/// Test that a struct auto-stronged by a call (see auto_strong_ret02.rs) can still be used as a
/// whole, i.e. that it is folded back before it is moved or returned,
/// see issue https://github.com/flux-rs/flux/issues/1714

pub struct Wrapper<'a> {
    #[flux::field(&mut usize{v: v >= 10})]
    pub inner: &'a mut usize,
}

#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> Wrapper)]
pub fn wrap(x: &mut usize) -> Wrapper<'_> {
    Wrapper { inner: x }
}

pub fn take(_w: Wrapper) {}

pub fn passed_by_value() {
    let mut blah = 10;
    let w = wrap(&mut blah);
    take(w);
}

pub fn moved_then_passed_by_value() {
    let mut blah = 10;
    let w = wrap(&mut blah);
    let v = w;
    take(v);
}

#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> Wrapper)]
pub fn returned(x: &mut usize) -> Wrapper<'_> {
    wrap(x)
}
