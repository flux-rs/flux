/// Test that folding an auto-stronged struct back to use it as a whole checks the writes made
/// through its fields, see issue https://github.com/flux-rs/flux/issues/1714

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
    *w.inner = 5;
    take(w); //~ ERROR type invariant may not hold
}

#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> Wrapper)]
pub fn returned(x: &mut usize) -> Wrapper<'_> {
    let w = wrap(x);
    *w.inner = 5;
    w //~ ERROR type invariant may not hold
}
