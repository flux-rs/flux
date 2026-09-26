/// Test that a `&mut` returned by a call can be turned into a reference before the end of the
/// block, e.g. by an unsize coercion, and still be used afterwards,
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

pub fn coerced() {
    let w = get();
    erase(w);
}

pub fn coerced_then_used() {
    let w = get();
    erase(w);
    w.n += 1;
}

pub fn written_then_coerced() {
    let w = get();
    w.n = 20;
    erase(w);
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

/// A pointer into a *field* of the returned `&mut`, coerced. Only the field is blocked, so the
/// location is still folded back at the end of the block.
pub fn field_coerced() {
    let p = get_pair();
    erase(&mut p.fst);
}
