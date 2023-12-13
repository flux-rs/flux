#[flux::sig(fn(n: usize) -> usize{v: v == n + 0xa})]
pub fn hex00(n: usize) -> usize {
    n + 10
}

#[flux::sig(fn(n: usize) -> usize{v: v == n + 0xA})]
pub fn hex01(n: usize) -> usize {
    n + 10
}

#[flux::sig(fn(n: usize) -> usize{v: v == n + 0x400})]
pub fn hex02(n: usize) -> usize {
    n + 1000 + 0x18
}


#[flux::sig(fn(n: usize) -> usize{v: v == n + 0o12})]
pub fn octal00(n: usize) -> usize {
    n + 10
}


#[flux::sig(fn(n: usize) -> usize{v: v == n + 0b1010})]
pub fn binary0(n: usize) -> usize {
    n + 10
}
