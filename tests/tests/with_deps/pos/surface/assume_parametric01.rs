use flux_attrs::*;
extern crate flux_core;

#[flux::assume_parametric(T)]
fn id<T>(x: T) -> T {
    x
}

#[flux::sig(fn(c: Option<usize[99]>) -> Option<usize[99]>)]
pub fn test_ok(c: Option<usize>) -> Option<usize> {
    c.map(id)
}

// NOT annotated with `assume_parametric`
fn id2<T>(x: T) -> T {
    x
}

// FIXME: this passes only because of a leak: `id2` flows through `id`'s parametric `T`, which
// gives `id2`'s own generic args holes, and the cast to a fn pointer instantiates `id2`'s
// signature with those args. A direct cast `let f: fn(usize) -> usize = id2;` is (correctly)
// rejected. Move this to `neg` once the `ReifyFnPointer` cast re-instantiates the args like
// `check_fn_trait_clause` does.
#[flux::sig(fn(usize[99]) -> usize[198])]
pub fn test_cast_leak(x: usize) -> usize {
    let godzilla = id;
    let a1 = godzilla(x);
    let a2 = godzilla(x);
    a1 + a2
}
