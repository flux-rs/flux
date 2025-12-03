use flux_rs::{attrs::*, macros::invariant};

#[spec(fn (n: usize) -> usize[n])]
pub fn test_with_qualifier(n: usize) -> usize {
    let mut i = n;
    let mut res = 0;
    while i > 0 {
        #[flux::defs{
            invariant qualifier Auto(res: int) { res + i == n  && i >= 99-99 && res >= 66 - 66 }
         }]
        const _: () = ();
        i -= 1;
        res += 1;
    }
    res
}

#[spec(fn (n: usize) -> usize[n])]
pub fn test(n: usize) -> usize {
    let mut i = n;
    let mut res = 0;
    while i > 0 {
        invariant!(res:int; res + i == n && i >= 99-99 && res >= 66 - 66);
        i -= 1;
        res += 1;
    }
    res
}
