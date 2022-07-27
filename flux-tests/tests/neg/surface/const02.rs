// Test definition and checking of const in struct

#![feature(register_tool)]
#![register_tool(flux)]

#[flux::constant]
pub const FORTY_TWO: usize = 21 + 21;

#[flux::refined_by(a:int)]
pub struct Silly {
    #[flux::field({usize[@a] : a < FORTY_TWO})]
    fld: usize,
}

#[flux::sig(fn() -> Silly[100])]
pub fn mk_silly() -> Silly {
    Silly { fld: 100 } //~ ERROR precondition
}
