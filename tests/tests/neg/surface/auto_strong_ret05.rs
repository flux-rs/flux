/// Test that a write through a `&mut` returned by a call is checked against the returned type
/// when the pointer is turned into a reference by an unsize coercion,
/// see issue https://github.com/flux-rs/flux/issues/1714

pub trait Sink {
    fn put(&mut self);
}

#[flux::refined_by(n: int)]
pub struct W {
    #[flux::field(usize[n])]
    pub n: usize,
}

impl Sink for W {
    fn put(&mut self) {}
}

#[flux::trusted]
#[flux::sig(fn () -> &mut W{v: v.n >= 10})]
pub fn get() -> &'static mut W {
    unimplemented!()
}

pub fn erase(_s: &mut dyn Sink) {}

pub fn written_then_coerced() {
    let w = get();
    w.n = 0;
    erase(w); //~ ERROR type invariant may not hold
}

#[flux::refined_by(fst: int)]
pub struct Pair {
    #[flux::field(W[fst])]
    pub fst: W,
}

#[flux::trusted]
#[flux::sig(fn () -> &mut Pair{v: v.fst >= 10})]
pub fn get_pair() -> &'static mut Pair {
    unimplemented!()
}

pub fn field_written_then_coerced() {
    let p = get_pair();
    p.fst.n = 0;
    erase(&mut p.fst); //~ ERROR type invariant may not hold
}
