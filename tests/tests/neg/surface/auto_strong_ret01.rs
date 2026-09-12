/// Test that a write through a `&mut` into a *field* of a `&mut` returned by a call is still
/// checked when the auto-strong pointer is folded back,
/// see issue https://github.com/flux-rs/flux/issues/1714

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

pub fn client() {
    let mut pair = Pair { fst: 10, snd: 0 };
    let p = returns_a_mut(&mut pair);
    let fst = &mut p.fst;
    *fst = 5;
} //~ ERROR type invariant may not hold
