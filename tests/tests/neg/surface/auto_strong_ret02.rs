/// Test that writes through a `&mut` nested inside a struct or tuple returned by a call are still
/// checked when the auto-strong pointer is folded back,
/// see issue https://github.com/flux-rs/flux/issues/1714

pub struct Wrapper<'a> {
    #[flux::field(&mut usize{v: v >= 10})]
    pub inner: &'a mut usize,
}

#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> Wrapper)]
pub fn wrap(x: &mut usize) -> Wrapper<'_> {
    Wrapper { inner: x }
}

pub fn struct_client() {
    let mut blah = 10;
    let w = wrap(&mut blah);
    *w.inner = 5;
} //~ ERROR type invariant may not hold

#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> (&mut usize{v: v >= 10}, usize[0]))]
pub fn tag(x: &mut usize) -> (&mut usize, usize) {
    (x, 0)
}

pub fn tuple_client() {
    let mut blah = 10;
    let (r, _n) = tag(&mut blah);
    *r = 5;
} //~ ERROR type invariant may not hold
