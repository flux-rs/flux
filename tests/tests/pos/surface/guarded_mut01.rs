#![allow(dead_code)]

// Several fields guarded at once. Each guard contributes its own variable to the binder on the
// folded type, so `fold` has to build a multi-variable binder.

#[flux::refined_by(a: int, b: int, c: int)]
#[flux::invariant(a <= b && a <= c)]
pub struct Three {
    #[flux::field(usize[a])]
    a: usize,
    #[flux::field(usize[b])]
    b: usize,
    #[flux::field(usize[c])]
    c: usize,
}

// two live borrows, both guards strong enough
#[flux::sig(fn(s: &mut Three[@me]) -> (&mut usize{v: me.a <= v}, &mut usize{v: me.a <= v}) ensures s: Three)]
pub fn test00(s: &mut Three) -> (&mut usize, &mut usize) {
    let Three { a: _, b, c } = s;
    (b, c)
}

// guards that pin the values exactly, so there is nothing to bind
#[flux::sig(fn(s: &mut Three[@me]) -> (&mut usize[me.b], &mut usize[me.c]) ensures s: Three)]
pub fn test01(s: &mut Three) -> (&mut usize, &mut usize) {
    let Three { a: _, b, c } = s;
    (b, c)
}

#[flux::sig(fn(s: &mut Three[@me]) -> &mut usize{v: me.a <= v} ensures s: Three{v: v.a == me.a && v.b == me.b})]
pub fn test02(s: &mut Three) -> &mut usize {
    let Three { a: _, b: _, c } = s;
    c
}

#[flux::sig(fn(s: &mut Three{v: v.a == 0}) ensures s: Three{v: v.a == 0})]
pub fn test02_client(s: &mut Three) {
    // let mut s = Three { a: 0, b: 1, c: 2 };
    let c = test02(s);
    *c += 1;
}
