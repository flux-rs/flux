#![flux::opts(check_overflow = "strict")]

#[flux::sig(fn(u32[@b0], (u32,)) -> u32)]
fn add(x: u32, (b0,): (u32,)) -> u32 {
    x + b0
}
