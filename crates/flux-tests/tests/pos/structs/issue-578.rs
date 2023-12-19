#[flux::sig(fn(bool[true]))]
fn assert(_: bool) {}

pub fn test() {
    let mut s: Vec<i32> = vec![];
    s.push(0);
    s.push(1);
    for v in &s {
        assert(*v >= 0);
    }
}
