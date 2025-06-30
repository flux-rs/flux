use flux_rs::attrs::*;

#[opaque]
struct S1 {
    x: i32,
}

fn opaque_struct01(s: S1) -> i32 {
    s.x //~ ERROR opaque
}

#[opaque]
struct S2(i32);

fn test(f: impl FnOnce(i32) -> S2) {}

fn opaque_struct02() {
    test(S2) //~ ERROR opaque
}
