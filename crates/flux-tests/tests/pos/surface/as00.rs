#[flux::trusted]
#[flux::sig(fn(n:u32) -> usize[n])]
pub fn as_usize(n: u32) -> usize {
    n as usize
}

#[flux::sig(fn(n:u32) -> usize[n])]
pub fn bar(n: u32) -> usize {
    as_usize(n)
}
