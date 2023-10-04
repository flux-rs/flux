#[flux::sig(fn(n:i32, Box<i32[n]>) -> i32[n+1])]
pub fn inc(_n: i32, b: Box<i32>) -> i32 {
    let x = *b;
    x + 1
}
