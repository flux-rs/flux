// Test that we accept nested qualified paths

use flux_rs::attrs::*;

trait Trait1 {
    type Assoc1: Trait2;
}

trait Trait2 {
    type Assoc2;
}

#[sig(fn(<<T as Trait1>::Assoc1 as Trait2>::Assoc2{v: true}))]
fn test<T: Trait1>(x: <<T as Trait1>::Assoc1 as Trait2>::Assoc2) {}
