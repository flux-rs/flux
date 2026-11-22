#[flux::trusted]
#[flux::sig(fn() -> i32[#x] ensures x > 0, x < 10)]
fn bounded() -> i32 {
    5
}

#[flux::sig(fn() -> i32{v: v > 0 && v < 10})]
fn use_bounded() -> i32 {
    bounded()
}
