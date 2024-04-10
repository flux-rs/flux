struct S<T> {
    f: T,
}

// Check that we can unfold and then fold back an owned struct with different substs
#[flux::sig(fn(S<i32{v: v > 0}>) -> i32{v: v >= 0})]
fn test00(mut s: S<i32>) -> i32 {
    s.f -= 1;
    &s; // trigger a fold
    s.f
}
