#[path = "../../lib/rmap.rs"]
mod rmap;
use rmap::RMap;

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let mut m = RMap::new();
    let k0 = 10;
    let k1 = 20;
    let k2 = 30;

    m.set(k0, 1);
    m.set(k1, 2);

    assert(*m.get(&k0).unwrap() == 1);
    assert(*m.get(&k1).unwrap() == 2);
    assert(*m.get(&k2).unwrap() == 3); //~ ERROR refinement type
}
