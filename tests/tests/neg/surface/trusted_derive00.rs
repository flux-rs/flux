// Test that an explicit `#[flux::trusted_derive(no)]` overrides the implicit trust that
// `#[flux::opaque]` grants, putting the derived code back under the checker.
#[derive(Debug, Hash)]
#[flux::opaque]
#[flux::trusted_derive(no)]
#[flux::refined_by(n: int)]
pub struct OptedIn(u32); //~ ERROR invalid use of opaque struct
                         //~| ERROR invalid use of opaque struct
