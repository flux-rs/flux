#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/range.rs"]
mod range;
use range::Rng;

#[flux::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

pub fn test() {
    let mut rng = Rng::new(10, 20);
    let _z = rng.next();

    // while let Some(val) = rng.next() {
    // assert(10 <= val && val < 20)
    // }
}
