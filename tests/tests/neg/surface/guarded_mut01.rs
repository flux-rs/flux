// Several fields guarded at once, where the guards are not enough to re-establish the invariant.

#[flux::refined_by(a: int, b: int, c: int)]
#[flux::invariant(a <= b && a <= c)] //~ NOTE this is the condition
struct Three {
    #[flux::field(usize[a])]
    a: usize,
    #[flux::field(usize[b])]
    b: usize,
    #[flux::field(usize[c])]
    c: usize,
}

#[flux::refined_by(a: int, b: int, c: int)]
#[flux::invariant(a <= b && b <= c)] //~ NOTE this is the condition
struct Ordered {
    #[flux::field(usize[a])]
    a: usize,
    #[flux::field(usize[b])]
    b: usize,
    #[flux::field(usize[c])]
    c: usize,
}

// only the first guard is strong enough
#[flux::sig(fn(s: &mut Three[@me]) -> (&mut usize{v: me.a <= v}, &mut usize) ensures s: Three)]
fn test00(s: &mut Three) -> (&mut usize, &mut usize) {
    let Three { a: _, b, c } = s;
    (b, c)
} //~ ERROR type invariant may not hold

// each guard is strong enough on its own, but they say nothing about how the two new values relate,
// so `b <= c` cannot be recovered
#[flux::sig(fn(s: &mut Ordered[@me]) -> (&mut usize{v: me.a <= v && v <= me.c}, &mut usize{v: me.a <= v && v <= me.c}) ensures s: Ordered)]
fn test01(s: &mut Ordered) -> (&mut usize, &mut usize) {
    let Ordered { a: _, b, c } = s;
    (b, c)
} //~ ERROR type invariant may not hold
