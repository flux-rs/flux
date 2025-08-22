// test that we correctly instantiate generics in the InferCtxt when checking
// trait subtyping

use flux_rs::attrs::*;

trait Trait {
    #[sig(fn(x: T, y: T) -> T[x])]
    fn method00<T>(x: T, y: T) -> T;
}

struct S;
impl Trait for S {
    #[sig(fn(x: S, y: S) -> S[x])]
    fn method00<S>(x: S, y: S) -> S {
        x
    }
}
