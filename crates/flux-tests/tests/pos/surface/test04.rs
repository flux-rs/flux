enum E {
    A,
}

struct S {
    f: i32,
}

#[flux::sig(fn(x: &strg S) -> E ensures x: S)]
fn foo(s: &mut S) -> E {
    baz(&mut s.f);
    E::A
}

fn baz(x: &mut i32) {}
