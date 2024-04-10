// #[path = "../../lib/rvec.rs"]
// mod rvec;
// use rvec::RVec;

#[flux::sig(fn (bool[true]))]
fn assert(_b: bool) {}

pub fn test() {
    let mut s: Vec<i32> = vec![];
    s.push(666);
    for v in &s {
        assert(*v >= 0);
    }
}
