extern crate flux_core;

// The block joining the branches of the `if` is a dummy join that we skip, but it is also the
// immediate dominator of the loop head.

pub fn test1(b: bool) {
    if b {}
    loop {}
}

pub fn test2(mut cur: usize) -> usize {
    if cur == 0 {
        cur = 1;
    }
    let x;
    loop {
        cur += 1;
        if cur % 2 == 0 {
            x = cur;
            break;
        }
    }
    x
}
