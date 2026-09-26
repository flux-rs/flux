/// Test that a `&mut` into a *field* of a `&mut` returned by a call is strong too, i.e. that
/// pointers with a non-empty projection into the auto-strong location are precise,
/// see issue https://github.com/flux-rs/flux/issues/1714

#[flux::sig(fn(x: bool[true]))]
pub fn assert(_x: bool) {}

#[flux::refined_by(fst: int, snd: int)]
pub struct Pair {
    #[flux::field(usize[fst])]
    pub fst: usize,
    #[flux::field(usize[snd])]
    pub snd: usize,
}

#[flux::sig(fn (p: &mut Pair{v: v.fst >= 10}) -> &mut Pair{v: v.fst >= 10})]
pub fn returns_a_mut(p: &mut Pair) -> &mut Pair {
    p
}

pub fn field_reads_are_equal() {
    let mut pair = Pair { fst: 10, snd: 0 };
    let p = returns_a_mut(&mut pair);
    let fst = &mut p.fst;
    let a = *fst;
    let b = *fst;
    assert(a == b)
}

pub fn field_read_after_write() {
    let mut pair = Pair { fst: 10, snd: 0 };
    let p = returns_a_mut(&mut pair);
    let fst = &mut p.fst;
    *fst = 20;
    assert(*fst == 20)
}
