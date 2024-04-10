struct S {
    f: i32,
}

fn take_shr_ref(s: &S) {}

#[flux::sig(fn(&S))]
fn test_shr_ref(s: &S) {
    if true {
        s.f;
    }
    take_shr_ref(s);
}

fn take_mut_ref(s: &mut S) {}

#[flux::sig(fn(&mut S))]
fn test_mut_ref(s: &mut S) {
    if true {
        s.f;
    }
    take_mut_ref(s)
}

#[flux::sig(fn(s: &strg S) ensures s: S)]
fn test_strg_ref(s: &mut S) {
    if true {
        s.f;
    }
}
