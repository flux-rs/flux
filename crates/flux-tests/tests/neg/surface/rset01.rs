#[path = "../../lib/rset.rs"]
mod rset;
use rset::RSet;

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let mut s = RSet::new();
    let v0 = 666;
    let v1 = 667;
    s.insert(v0);
    assert(s.contains(&v0));
    assert(s.contains(&v1)); //~ ERROR refinement type
}

#[flux::sig(fn () -> RSet<i32{v:667<=v}>)]
pub fn test1() -> RSet<i32> {
    let mut s = RSet::new();
    let v0 = 666;
    let v1 = 667;
    s.insert(v0);
    s.insert(v1);
    s //~ ERROR refinement type
}
