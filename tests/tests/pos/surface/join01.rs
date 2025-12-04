// #[flux::sig(fn(&mut i32[0], bool) -> i32{v : v >= 0})]
#[flux::sig(fn(r1: &mut i32[0], bool) -> i32{v : v >= 0} ensures r1: i32[0])]
pub fn foo(r1: &mut i32, b: bool) -> i32 {
    let mut x = 1;
    let r;
    if b {
        r = &mut *r1;
    } else {
        r = &mut x;
    }
    *r
}
