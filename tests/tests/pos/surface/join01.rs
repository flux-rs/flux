// NOTE: this test fails if we add a "trivial" ensures clause;
// hence we restrict auto-strong to lifted-signatures in
// https://github.com/flux-rs/flux/pull/1392
// #[flux::sig(fn(r1: &mut i32[0], bool) -> i32{v : v >= 0} ensures r1: i32[0])]

#[flux::sig(fn(&mut i32[0], bool) -> i32{v : v >= 0})]
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
