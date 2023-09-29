#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]

#[path = "../../lib/rmapk.rs"]
mod rmapk;
use rmapk::RMap;

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let mut m = RMap::new();
    m.set(10, 1);
    m.set(20, 2);

    assert(1 + 1 == 2);
    assert(m.get(20).unwrap() == 2);
    assert(m.lookup(10) == 1);
    assert(m.lookup(20) == 2);
    assert(m.contains(10));
    assert(m.contains(30)); //~ ERROR refinement type
}
