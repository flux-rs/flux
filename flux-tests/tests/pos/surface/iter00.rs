#![feature(register_tool)]
#![register_tool(flux)]

#[path = "../../lib/range.rs"]
mod range;
use range::Rng;

#[flux::sig(fn(bool[true]) -> ())]
pub fn assert(_b: bool) {}

pub fn test(n: i32) {
    let mut rng = Rng::new(n, n + 100);
    while let Some(val) = rng.next() {
        assert(n <= val && val < n + 100)
    }
}
