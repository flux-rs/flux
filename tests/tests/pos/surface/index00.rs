#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

pub fn test00() {
    let x = 1;
    let y = 2;
    assert(x + 1 == y);
}

#[flux::sig(fn five() -> usize[5])]
pub fn five() -> usize {
    let x = 2;
    let y = 3;
    x + y
}

#[flux::sig(fn(n:usize) -> usize[n+1])]
pub fn incr(n: usize) -> usize {
    n + 1
}

pub fn test01() {
    let a = five();
    let b = incr(a);
    assert(b == 6);
}
