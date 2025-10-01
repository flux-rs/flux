#[path = "../../lib/rset.rs"]
mod rset;
use rset::RSet;

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test_insert() {
    let mut s = RSet::new();
    let v0 = 666;
    let v1 = 667;
    s.insert(v0);
    assert(s.contains(&v0));
    assert(!s.contains(&v1));
}

pub fn test_union() {
    let mut s1 = RSet::new();
    let mut s2 = RSet::new();
    let v0 = 666;
    let v1 = 667;
    s1.insert(v0);
    s2.insert(v1);
    let s3 = s1.union(&s2);
    assert(s3.contains(&v0));
    assert(s3.contains(&v1));
}

pub fn test_intersection() {
    let mut s1 = RSet::new();
    let mut s2 = RSet::new();
    let v0 = 666;
    let v1 = 667;
    let v2 = 999;
    s1.insert(v0);
    s1.insert(v2);

    s2.insert(v1);
    s2.insert(v2);

    let s3 = s1.intersection(&s2);
    assert(!s3.contains(&v0));
    assert(!s3.contains(&v1));
    assert(s3.contains(&v2));
}

#[flux::sig(fn () -> RSet<i32{v:666<=v}>)]
pub fn test1() -> RSet<i32> {
    let mut s = RSet::new();
    let v0 = 666;
    let v1 = 667;
    s.insert(v0);
    s.insert(v1);
    s
}
