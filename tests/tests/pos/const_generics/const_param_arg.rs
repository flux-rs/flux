// Test support for const generic parameters used in argument position inside refinements. These
// are parsed as types and disambiguated during name resolution.

use flux_rs::attrs::*;

struct S1<const N: usize> {}

#[refined_by()]
struct S2<const M: usize> {
    #[field(S1<M>)]
    f: S1<M>,
}

trait Trait1<const N: usize> {
    #[spec(fn(S1<N>))]
    fn method(x: S1<N>);
}

#[assoc(fn f(self: Self::Assoc) -> bool)]
trait Trait2<const N: usize> {
    type Assoc;

    #[spec(fn(x: Self::Assoc{ <Self as Trait2<N>>::f(x) }))]
    fn fun(x: Self::Assoc);
}
