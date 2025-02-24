use flux_rs::attrs::*;

#[refined_by(n: int)]
#[invariant(n > 0)]
struct A {
    #[field(i32[n])]
    f: i32,
}

fn baz(a: A) {
    flux_rs::assert(a.f > 0); // uh-oh
}

fn foo() {
    let mut a = A { f: 1 };
    a.f -= 1; // this is fine, we don't need to preserve the invariant while unfolded.
    baz(a); //~ ERROR type invariant may not hold
}
