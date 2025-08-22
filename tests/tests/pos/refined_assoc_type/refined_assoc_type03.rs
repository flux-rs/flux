// test that we can use associated type as sorts

use flux_rs::attrs::*;

trait Trait1 {
    type Assoc1: Trait2;
}

trait Trait2 {
    type Assoc2;
}

#[refined_by(x: <<T as Trait1>::Assoc1 as Trait2>::Assoc2)]
struct S1<T: Trait1> {
    #[field(<<T as Trait1>::Assoc1 as Trait2>::Assoc2[x])]
    x: <<T as Trait1>::Assoc1 as Trait2>::Assoc2,
}

#[refined_by(x: <T::Assoc1 as Trait2>::Assoc2)]
struct S2<T: Trait1> {
    #[field(<T::Assoc1 as Trait2>::Assoc2[x])]
    x: <T::Assoc1 as Trait2>::Assoc2,
}
