#[flux::sig(fn() -> bool)]
pub fn toss() -> bool {
    true
}

#[flux::sig(fn(k: i32{0 <= k}) -> i32[0])]
pub fn test(mut k: i32) -> i32 {
    while toss() && k < i32::MAX - 1 {
        k += 1;
    }
    while k > 0 {
        k -= 1;
    }
    k
}
