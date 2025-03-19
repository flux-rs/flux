// Test that sorts in early generic refinements are correctly instantiated
//
// see https://github.com/flux-rs/flux/issues/1036

use flux_rs::attrs::*;

trait Trait {
    type Assoc;

    #[sig(fn(x: Self::Assoc) -> Self::Assoc[x])]
    fn test00(x: Self::Assoc) -> Self::Assoc;
}

struct S;

impl Trait for S {
    type Assoc = bool;

    // weird way to write `x` just there's something to prove
    #[sig(fn(x: bool) -> bool[if x { x && x } else { x }])]
    fn test00(x: bool) -> bool {
        !x //~ERROR refinement type error
    }
}
