use flux_attrs::*;

// Regression test: kvar on a type parameter nested inside a `Ty`-valued base type (here the tuple `(T,)`)
// must survive projection normalization. Previously `TVarSubst` dropped the refinement while computing the
// impl substitution for `<(T,) as Get>::Output`, so the result came back as a bare `i32`.

trait Get {
    type Output;
}

impl<T> Get for (T,) {
    type Output = T;
}

#[spec(fn(x: (T,)) -> _)]
fn get<T>(x: (T,)) -> <(T,) as Get>::Output {
    x.0
}

#[spec(fn(x: i32{v: v > 0}) -> i32{v: v > 0})]
fn test(x: i32) -> i32 {
    get((x,))
}
