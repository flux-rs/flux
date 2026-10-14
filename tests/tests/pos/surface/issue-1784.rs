extern crate flux_core;

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
