use flux_attrs::*;

// Negative counterpart of pos/surface/associated_type02.rs: the refinement must not be
// fabricated when the input carries none, so this postcondition is genuinely unprovable.

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

#[spec(fn(x: i32{v: v >= 0}) -> i32{v: v > 0})]
fn test(x: i32) -> i32 {
    get((x,)) //~ ERROR refinement type
}
