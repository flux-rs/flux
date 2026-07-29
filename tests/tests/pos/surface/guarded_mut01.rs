// Several fields guarded at once. Each guard contributes its own variable to the binder on the
// folded type, so `fold` has to build a multi-variable binder.

#[flux::refined_by(a: int, b: int, c: int)]
#[flux::invariant(a <= b && a <= c)]
struct Three {
    #[flux::field(usize[a])]
    a: usize,
    #[flux::field(usize[b])]
    b: usize,
    #[flux::field(usize[c])]
    c: usize,
}

// two live borrows, both guards strong enough
#[flux::sig(fn(s: &mut Three[@me]) -> (&mut usize{v: me.a <= v}, &mut usize{v: me.a <= v}) ensures s: Three)]
fn test00(s: &mut Three) -> (&mut usize, &mut usize) {
    let Three { a: _, b, c } = s;
    (b, c)
}

// guards that pin the values exactly, so there is nothing to bind
#[flux::sig(fn(s: &mut Three[@me]) -> (&mut usize[me.b], &mut usize[me.c]) ensures s: Three)]
fn test01(s: &mut Three) -> (&mut usize, &mut usize) {
    let Three { a: _, b, c } = s;
    (b, c)
}
