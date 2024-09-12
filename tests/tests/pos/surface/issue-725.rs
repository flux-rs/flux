#![allow(unused)]

// TODO: support something like the below signature!
// #[flux::sig(fn () -> usize[11])]

struct Bob {}

fn test1() -> usize {
    let [x, y] = [1, 10];
    x + y
}

fn test2() -> Bob {
    let b0 = Bob {};
    let b1 = Bob {};
    let [x, y] = [b0, b1];
    x
}
