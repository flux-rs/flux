// Test that derive-generated code is checked by default, i.e. unless the type carries
// `#[flux::trusted_derive]`.

// No `#[flux::trusted_derive]`: the derived `Debug` and `Hash` both read the opaque representation.
#[derive(Debug, Hash)]
#[flux::opaque]
#[flux::refined_by(n: int)]
pub struct NoAttr(u32); //~ ERROR invalid use of opaque struct
                        //~| ERROR invalid use of opaque struct

// `#[flux::trusted_derive(no)]` explicitly opts back in to checking.
#[derive(Debug, Hash)]
#[flux::opaque]
#[flux::trusted_derive(no)]
#[flux::refined_by(n: int)]
pub struct OptedIn(u32); //~ ERROR invalid use of opaque struct
                         //~| ERROR invalid use of opaque struct
