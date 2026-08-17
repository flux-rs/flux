/// Test that a write through a `&mut` nested inside a struct returned by a call is checked when
/// the struct is folded before the end of the block,
/// see issue https://github.com/flux-rs/flux/issues/1714

pub struct Wrapper<'a> {
    #[flux::field(&mut usize{v: v >= 10})]
    pub inner: &'a mut usize,
}

#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> Wrapper)]
pub fn wrap(x: &mut usize) -> Wrapper<'_> {
    Wrapper { inner: x }
}

pub trait Sink {
    fn put(&mut self);
}

impl Sink for Wrapper<'_> {
    fn put(&mut self) {
        *self.inner = 20;
    }
}

pub fn erase(_s: &mut dyn Sink) {}

#[flux::sig(fn (x: &mut usize{v: v >= 10}))]
pub fn borrowed_and_coerced(x: &mut usize) {
    let mut w = wrap(x);
    *w.inner = 5;
    erase(&mut w); //~ ERROR type invariant may not hold
}
