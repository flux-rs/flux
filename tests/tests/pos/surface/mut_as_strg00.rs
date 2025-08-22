#[flux::sig(fn (x: &mut i32[@n]) ensures x: i32[n+1])]
pub fn incr(x: &mut i32) {
    *x += 1;
}

#[flux::sig(fn (x: &mut i32{v: v> 999}) ensures x: i32)]
pub fn bincr(_x: &mut i32) {}

#[flux::sig(fn () -> i32[11])]
pub fn client_safe() -> i32 {
    let mut p = 10;
    incr(&mut p);
    p
}
