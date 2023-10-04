#[path = "../../lib/rmap.rs"]
mod rmap;
use rmap::RMap;

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let mut m = RMap::new();
    m.set(10, 1);
    m.set(20, 2);

    assert(1 + 1 == 2);
    assert(m.get(10).unwrap() == 1);
    assert(m.get(20).unwrap() == 2);
    assert(m.get(30).unwrap() == 3); //~ ERROR refinement type
}
