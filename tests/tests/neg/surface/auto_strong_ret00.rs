/// Test that writes through a `&mut` returned by a call are still checked against the type of
/// the reference when the auto-strong pointer is folded back,
/// see issue https://github.com/flux-rs/flux/issues/1714
#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> &mut usize{v: v >= 10})]
pub fn returns_a_mut(x: &mut usize) -> &mut usize {
    x
}

#[flux::sig(fn () -> usize{v: v >= 10})]
pub fn client() -> usize {
    let mut blah = 10;
    let tmp = returns_a_mut(&mut blah);
    *tmp = 5;
    blah
} //~ ERROR type invariant may not hold
