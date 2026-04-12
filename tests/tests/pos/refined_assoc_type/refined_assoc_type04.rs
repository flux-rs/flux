// Test that we resolve type paths in associated refinements in a trait definition

use flux_attrs::*;

#[reft(fn p(x: <Self as Trait>::Assoc) -> bool)]
trait Trait {
    type Assoc;
}
