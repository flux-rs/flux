#[path = "../../lib/rrange.rs"]
mod range;
use range::{Rng, RngIter};

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

pub fn test_next() {
    let mut rng = RngIter::new(10, 15);
    while let Some(val) = rng.next() {
        assert(10 <= val && val < 15)
    }
}

pub fn test_for() {
    for val in Rng::new(110, 115) {
        assert(110 <= val && val < 115)
    }
}
