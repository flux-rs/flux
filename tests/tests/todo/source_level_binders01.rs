extern crate flux_alloc;

#[flux_rs::spec(fn (n:usize) -> Vec<usize>[n])]
pub fn test1(n: usize) -> Vec<usize> {
    let mut res = Vec::new();
    let mut i = 0;
    while i < n {
        res.push(i);
        i += 1;
    }
    return res;
}
