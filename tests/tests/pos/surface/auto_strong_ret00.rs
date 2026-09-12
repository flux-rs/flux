/// Test that a `&mut` returned by a call is automatically treated as a strong reference,
/// see issue https://github.com/flux-rs/flux/issues/1714

#[flux::sig(fn(x: bool[true]))]
pub fn assert(_x: bool) {}

#[flux::sig(fn (x: &mut usize{v: v >= 10}) -> &mut usize{v: v >= 10})]
pub fn returns_a_mut(x: &mut usize) -> &mut usize {
    x
}

pub fn reads_are_equal() {
    let mut blah = 10;
    let tmp = returns_a_mut(&mut blah);
    let a = *tmp;
    let b = *tmp;
    assert(a == b)
}

pub fn read_after_write() {
    let mut blah = 10;
    let tmp = returns_a_mut(&mut blah);
    *tmp = 20;
    assert(*tmp == 20)
}

pub fn write_in_branch(b: bool) {
    let mut blah = 10;
    let tmp = returns_a_mut(&mut blah);
    if b {
        *tmp = 20;
    }
    assert(*tmp >= 10)
}

/// The pointer is folded back before it reaches the join point where both calls meet.
pub fn call_in_branch(b: bool) {
    let mut blah = 10;
    let tmp = if b { returns_a_mut(&mut blah) } else { returns_a_mut(&mut blah) };
    assert(*tmp >= 10)
}
