/// Test that a `&mut` nested inside a struct or tuple returned by a call is auto-stronged too,
/// see issue https://github.com/flux-rs/flux/issues/1714

#[flux::sig(fn(x: bool[true]))]
pub fn assert(_x: bool) {}

pub struct Wrapper<'a> {
    #[flux::field(&mut usize{v: v >= 10})]
    pub inner: &'a mut usize,
}

#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> Wrapper)]
pub fn wrap(x: &mut usize) -> Wrapper<'_> {
    Wrapper { inner: x }
}

pub fn struct_field_reads_are_equal() {
    let mut blah = 10;
    let w = wrap(&mut blah);
    let a = *w.inner;
    let b = *w.inner;
    assert(a == b)
}

pub fn struct_field_read_after_write() {
    let mut blah = 10;
    let w = wrap(&mut blah);
    *w.inner = 20;
    assert(*w.inner == 20)
}

#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> (&mut usize{v: v >= 10}, usize[0]))]
pub fn tag(x: &mut usize) -> (&mut usize, usize) {
    (x, 0)
}

pub fn tuple_field_read_after_write() {
    let mut blah = 10;
    let (r, _n) = tag(&mut blah);
    *r = 20;
    assert(*r == 20)
}
