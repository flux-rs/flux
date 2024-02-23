// ignore-test: ignored until we implement trait bounds properly
#![flux::cfg(scrape_quals = true)]

#[path = "../../lib/rset.rs"]
mod rset;
use rset::RSet;

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let mut s: RSet<i32> = RSet::new();
    s.insert(10);
    s.insert(20);
    s.insert(30);

    for v in s.iter() {
        assert(*v >= 10);
    }
}
