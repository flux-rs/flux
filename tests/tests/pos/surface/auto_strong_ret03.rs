/// Test that a `&mut` nested inside a struct returned by a call is folded back when the struct
/// itself is folded, before the end of the block,
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

/// The unsize coercion is a statement, so it folds the struct while the pointer to the nested
/// `&mut` is still around.
#[flux::sig(fn (x: &mut usize{v: v >= 10}))]
pub fn borrowed_and_coerced(x: &mut usize) {
    erase(&mut wrap(x));
}
