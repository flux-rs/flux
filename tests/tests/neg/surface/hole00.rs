// Test we report an error for holes in positions where they cannot be filled

use flux_attrs::*;

#[assoc(fn f(self: Self::Assoc) -> bool)]
trait Trait<const N: usize> {
    type Assoc;

    #[spec(fn(x: Self::Assoc{ <Self as Trait<_>>::f(x) }))] //~ ERROR invalid use of `_`
    fn fun(x: Self::Assoc);
}

#[assoc(fn g(self: <Self as Trait2<_>>::Assoc) -> bool)] //~ ERROR invalid use of `_`
trait Trait2<const N: usize> {
    type Assoc;
}
